module Main where

import System.Console.ANSI
import System.Exit (exitSuccess)
import TypeReconstruction hiding (main)
import Parser


main :: IO ()
main = setTitle "TypeReconstruction - Repl" >> loop

-- | REPL with variable context
loop :: IO ()
loop = do
  colorize Blue $ putStr "λ>"
  str <- getLine
  case parseStmt str of
    Left err -> print err >> loop
    Right stmt -> evalStmt stmt >> loop


-- | evaluate a Statement
evalStmt :: Stmt -> IO ()
evalStmt Quit = putStrLn "Bye bye" >> exitSuccess
evalStmt Help = help
evalStmt (Constraints t) = case runConstraintCollection t of
         (Left err) -> colorize Red $ print err
         (Right eqs) -> do
           putStr $ show t
           colorize Green $ putStr " : "
           putStr "α₁ with "
           print eqs
evalStmt (Check t) = case typeCheck t of
        (Left err) -> colorize Red $ print err
        (Right eqs) -> do
          putStr $ show t
          colorize Green $ putStr " : "
          print $ getStart eqs

-- | Set and reset color for a given IO-action
colorize :: Color -> IO () -> IO ()
colorize c m = setSGR [SetColor Foreground Vivid c] >> m >> setSGR [Reset]

help :: IO ()
help = do
  putStrLn "Type a lambda term (may involve addition) to check its type."
  putStrLn "Options:"
  putStrLn "  :q to exit"
  putStrLn "  :c to show set of constraints for a term"
  putStrLn "  :h to display this information"
