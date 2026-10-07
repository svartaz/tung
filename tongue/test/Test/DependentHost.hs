{-# LANGUAGE OverloadedStrings #-}

-- runner deeds beyond the console: files, arguments, environment, exit,
-- processes, tasks, and the web server, against a simulated world.
module Test.DependentHost (group) where

import Data.List (isPrefixOf)
import Data.Map.Strict qualified as Map
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent.Source (SourceProgram)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_host.tung"
  library <- loadLibrary ["_foreign.tung", "deed/file.tung", "ilk/one.tung", "ilk/maybe.tung", "ilk/product.tung", "ilk/sum.tung"]
  Harness.group "dependent_host" (tests (compileWith library "dependent_host.tung") example)

tests :: (String -> Either String SourceProgram) -> String -> [Test]
tests compiled example =
  [ expectEq "the host example runneth every deed in order" (Right (Right 0, "saved\nno file absent.txt\nfrom a task\nung\n", Map.fromList [("note.txt", "saved")])) do
      (status, after) <- run example world
      pure (status, worldOutput after, worldFiles after),
    expectEq "an environment variable is an maybe" (Right (Right 0, "hello\nabsent\n")) $
      output
        ( host
            ++ "let environment:[text, (text maybe) deed] ≔ 'environment' fremmed\n"
            ++ "let lookup:[text, 𝟙 deed] ≔ {name ^ (name environment) deed_bind {none ^ 'absent' line, worth some ^ worth line}}\n"
            ++ "let main:𝟙 deed ≔ ('GREETING' lookup) then ('OTHER' lookup)\n"
        )
        world {worldEnvironment = [("GREETING", "hello")]},
    expectEq "exit endeth the run with its status" (Right (Right 3, "before\n")) $
      fmap worldOutput <$> run (host ++ "let exit:[@a:*, ℕ, a deed] ≔ 'exit' fremmed\nlet main:𝟙 deed ≔ ('before' line) then (3 exit)\n") world,
    expectEq "a failed task hath no result" (Right (Right 0, "no result\n")) $
      output (host ++ "let exit:[@a:*, ℕ, a deed] ≔ 'exit' fremmed\nlet main:𝟙 deed ≔ (3 exit) fork $ await\n") world
  ]
  where
    host = unlines (takeWhile (not . isPrefixOf "let main:") (lines example))
    run source start = compiled source >>= runWorld start
    output source start = fmap worldOutput <$> run source start
