module Main where

import LexGrammar
import ParGrammar
import AbsGrammar
import TypeChecker
import Interpreter
import ErrM
import System.IO
import System.Environment 
import qualified Data.Map as M

main :: IO ()
main = do
  args <- getArgs
  source <- readFile (args !! 0)
  case pProgram (myLexer source) of
    Bad err -> do
      putStrLn "Syntax error"
      putStrLn err
    Ok ast -> do
      typeCheckResult <- runTypeChecker (M.empty, M.empty) (checkProgram ast)
      case typeCheckResult of
        (Left errTypeChecker, _) -> putStrLn errTypeChecker
        (Right _, _) -> do 
          interpretResult <- runInterpreter (0, M.empty) (interpretProgram ast)
          case interpretResult of
            (Left errInterpreter, _) -> do
              putStrLn "Runtime Error:"
              putStrLn errInterpreter
            (Right _, _) -> do
              putStrLn "Program Succeeded"
  
