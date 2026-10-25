module Main where

import Test.Dependent qualified as Dependent
import Test.DependentClass qualified as DependentClass
import Test.DependentEffect qualified as DependentEffect
import Test.DependentField qualified as DependentField
import Test.DependentHost qualified as DependentHost
import Test.DependentInductive qualified as DependentInductive
import Test.DependentInductiveSource qualified as DependentInductiveSource
import Test.DependentList qualified as DependentList
import Test.DependentLiteral qualified as DependentLiteral
import Test.DependentMatch qualified as DependentMatch
import Test.DependentModule qualified as DependentModule
import Test.DependentRecursion qualified as DependentRecursion
import Test.DependentSource qualified as DependentSource
import Test.Diagnostic qualified as Diagnostic
import Test.Evaluate qualified as Evaluate
import Test.Format qualified as Format
import Test.Harness (runGroups)
import Test.HarnessTests qualified as HarnessTests
import Test.Integration qualified as Integration
import Test.Library qualified as Library
import Test.Name qualified as Name
import Test.Parse qualified as Parse
import Test.Program qualified as Program
import Test.Project qualified as Project
import Test.Standard qualified as Standard
import Test.Token qualified as Token
import Test.Type qualified as Type
import Test.Validate qualified as Validate

main :: IO ()
main =
  runGroups
    [ ("harness", HarnessTests.group),
      ("token", Token.group),
      ("parse", Parse.group),
      ("format", Format.group),
      ("validate", Validate.group),
      ("project", Project.group),
      ("library", Library.group),
      ("type", Type.group),
      ("name", Name.group),
      ("evaluate", Evaluate.group),
      ("standard", Standard.group),
      ("program", Program.group),
      ("dependent", Dependent.group),
      ("dependent-inductive", DependentInductive.group),
      ("dependent-inductive-source", DependentInductiveSource.group),
      ("dependent_effect", DependentEffect.group),
      ("dependent-class", DependentClass.group),
      ("dependent_host", DependentHost.group),
      ("dependent_list", DependentList.group),
      ("dependent-literal", DependentLiteral.group),
      ("dependent_match", DependentMatch.group),
      ("dependent-module", DependentModule.group),
      ("dependent-field", DependentField.group),
      ("dependent-recursion", DependentRecursion.group),
      ("dependent-source", DependentSource.group),
      ("diagnostic", Diagnostic.group),
      ("integration", Integration.group)
    ]
