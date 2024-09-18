package fix

import org.scalatest.funsuite.AnyFunSuiteLike
import scalafix.testkit.AbstractSemanticRuleSuite

class ScaluzziSuite extends AbstractSemanticRuleSuite with AnyFunSuiteLike {
  runAllTests()
}
