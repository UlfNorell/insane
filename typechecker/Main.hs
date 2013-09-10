
module Main where

import System.Environment

import Syntax.Abs
import Syntax.Par
import Syntax.Layout
import Syntax.ErrM
import Syntax.Print
import Syntax.Internal

import TypeChecker
import TypeChecker.Monad

checkFile :: FilePath -> IO ()
checkFile file = do
    s <- readFile file
    case pProgram $ resolveLayout True $ myLexer s of
	Bad s	-> putStrLn $ "Parse error: " ++ s
	Ok p	-> do
	    r <- runTC $ checkProgram p
	    case r of
		Left err -> print err
		Right () -> putStrLn "OK"

main = do
    args <- getArgs
    prog <- getProgName
    case args of
	[file]  -> checkFile file
	_	-> putStrLn $ "Usage: " ++ prog ++ " FILE"

