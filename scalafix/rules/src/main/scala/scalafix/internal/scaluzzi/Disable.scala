package scalafix.internal.scaluzzi

import metaconfig.Configured
import scalafix.v1._

import scala.annotation.tailrec
import scala.meta._
import scala.meta.transversers.Traverser

final case class Disable(config: DisableConfig) extends SemanticRule("Disable") {

  import Disable._

  override def description: String =
    "Linter that reports an error on a configurable set of symbols."

  override def withConfiguration(config: Configuration): Configured[Rule] =
    config.conf
      .getOrElse("disable", "Disable")(this.config)
      .map(newConfig => Disable(newConfig))

  private val safeBlocks = new DisableSymbolMatcher(config.allSafeBlocks)
  private val disabledSymbolInSynthetics =
    new DisableSymbolMatcher(config.ifSynthetic)

  private def createLintMessage(
      symbol: Symbol,
      disabled: DisabledSymbol,
      pos: Position,
      details: String = ""): Diagnostic = {
    val message = disabled.message.getOrElse(
      s"${symbol.displayName} is disabled$details")

    val id = disabled.id.getOrElse(symbol.displayName)

    Diagnostic(id, message, pos)
  }

  private def checkTree(implicit doc: SemanticDocument): Seq[Diagnostic] = {
    def filterBlockedSymbolsInBlock(
        blockedSymbols: List[DisabledSymbol],
        block: Tree): List[DisabledSymbol] = {
      val symbolBlock = block.symbol
      val symbolsInMatchedBlocks = config.unlessInside.flatMap(u =>
          if (u.safeBlocks.exists(_.matches(symbolBlock))) u.symbols
          else List.empty
        )
      blockedSymbols.filterNot(symbolsInMatchedBlocks.contains)
    }

    @tailrec
    def skipTermSelect(term: Term): Boolean = term match {
      case _: Term.Name => true
      case Term.Select(q, _) => skipTermSelect(q)
      case _ => false
    }

    def handleName(t: Name, blockedSymbols: List[DisabledSymbol])
      : Either[Diagnostic, List[DisabledSymbol]] = {
      val s = t.symbol
      new DisableSymbolMatcher(blockedSymbols).findMatch(s) match {
        case Some(disabled) if s.displayName != "<init>" =>
          Left(createLintMessage(s, disabled, t.pos))
        case _ =>
          Right(blockedSymbols)
      }
    }

    new ContextTraverser(config.allDisabledSymbols)({
      case (_: Import, _) => Right(List.empty)
      case (Term.Select(q, name), blockedSymbols) if skipTermSelect(q) =>
        handleName(name, blockedSymbols)
      case (Type.Select(q, name), blockedSymbols) if skipTermSelect(q) =>
        handleName(name, blockedSymbols)
      case (
          Term.Apply.After_4_6_0(
            Term.Select(block @ safeBlocks(_, _), Term.Name("apply")),
            _
          ),
          blockedSymbols
          ) =>
        Right(filterBlockedSymbolsInBlock(blockedSymbols, block)) // <Block>.apply
      case (Term.Apply.After_4_6_0(block @ safeBlocks(_, _), _), blockedSymbols) =>
        Right(filterBlockedSymbolsInBlock(blockedSymbols, block)) // <Block>(...)
      case (_: Defn.Def, _) =>
        Right(config.allDisabledSymbols) // reset blocked symbols in def
      case (_: Term.Function, _) =>
        Right(config.allDisabledSymbols) // reset blocked symbols in (...) => (...)
      case (t: Name, blockedSymbols) =>
        handleName(t, blockedSymbols)
    }).result(doc.tree)
  }

  private def checkSynthetics(implicit doc: SemanticDocument): Seq[Diagnostic] = {
    val terms = doc.tree.collect { case t: Term => t }
    terms.flatMap { term =>
      val symbolsWithTrees = term.synthetics.flatMap {
        case tree @ TypeApplyTree(_, typeArguments) =>
          typeArguments.flatMap(extractSymbols).map((_, tree))
        case tree =>
          tree.symbol.toList.map((_, tree))
      }
      symbolsWithTrees.collect { case (disabledSymbolInSynthetics(symbol, ds), tree) =>
        createLintMessage(symbol, ds, term.pos, s" and it got inferred as `$tree`")
      }
    }
  }


  def this() = this(config = DisableConfig())

  override def fix(implicit doc: SemanticDocument): Patch =
    (checkTree(doc) ++ checkSynthetics(doc)).map(Patch.lint).asPatch

}

object Disable {

  /**
   * A tree traverser to collect values with a custom context.
   * At every tree node, either builds a new Context or returns a new Value to accumulate.
   * To collect all accumulated values, use result(Tree).
   */
  private class ContextTraverser[Value, Context](initContext: Context)(
    fn: PartialFunction[(Tree, Context), Either[Value, Context]])
    extends Traverser {
    private var context: Context = initContext
    private val buf = scala.collection.mutable.ListBuffer[Value]()

    private val liftedFn = fn.lift

    override def apply(tree: Tree): Unit = {
      liftedFn((tree, context)) match {
        case Some(Left(res)) =>
          buf += res
        case Some(Right(newContext)) =>
          val oldContext = context
          context = newContext
          super.apply(tree)
          context = oldContext
        case None =>
          super.apply(tree)
      }
    }

    def result(tree: Tree): List[Value] = {
      context = initContext
      buf.clear()
      apply(tree)
      buf.toList
    }
  }

  final class DisableSymbolMatcher(symbols: List[DisabledSymbol]) {
    def findMatch(symbol: Symbol): Option[DisabledSymbol] =
      symbols.find(_.matches(symbol))

    def unapply(tree: Tree)(implicit doc: SemanticDocument): Option[(Tree, DisabledSymbol)] =
      findMatch(tree.symbol).map(ds => (tree, ds))

    def unapply(symbol: Symbol): Option[(Symbol, DisabledSymbol)] =
      findMatch(symbol).map(ds => (symbol, ds))
  }

  def extractSymbols(tpe: SemanticType): List[Symbol] =
    tpe match {
      case TypeRef(prefix, symbol, typeArguments) =>
        symbol :: extractSymbols(prefix) ::: typeArguments.flatMap(extractSymbols)
      case SingleType(prefix, symbol) =>
        symbol :: extractSymbols(prefix)
      case ThisType(symbol) => symbol :: Nil
      case SuperType(prefix, symbol) =>
        symbol :: extractSymbols(prefix)
      case ConstantType(_) =>
        Nil
      case IntersectionType(types) =>
        types.flatMap(extractSymbols)
      case UnionType(types) =>
        types.flatMap(extractSymbols)
      case WithType(types) =>
        types flatMap extractSymbols
      case StructuralType(tpe, _) =>
        extractSymbols(tpe)
      case AnnotatedType(_, tpe) =>
        extractSymbols(tpe)
      case ExistentialType(tpe, _) =>
        extractSymbols(tpe)
      case UniversalType(typeParameters, tpe) =>
        typeParameters.map(_.symbol) ::: extractSymbols(tpe)
      case ByNameType(tpe) =>
        extractSymbols(tpe)
      case RepeatedType(tpe) =>
        extractSymbols(tpe)
      case _ => Nil
    }
}