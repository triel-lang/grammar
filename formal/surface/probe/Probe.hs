-- Probe of the export of parse trees: reads the tree written by tree.py, builds
-- both variants of ptree (formal/surface/Surface_Probe.thy), calls the exported
-- functions and prints one line per result, a text as the decimal codes of its
-- characters, an error as the text of the exception (a Haskell string literal).
-- The last line holds the texts of (a) of the first variant as they are, in the
-- encoding of the locale. Usage: probe TREE
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Data.Char (chr, ord)
import System.Environment (getArgs)
import qualified TRIEL_Surface_Probe as P

tree :: ([Integer] -> t) -> [[String]] -> (P.Ptree t, [[String]])
tree _ (["A"] : ls) = (P.Absent, ls)
tree f (("L" : n : cs) : ls) = (P.Leaf n (f (map read cs)), ls)
tree f (["N", r, k] : ls) = go (read k :: Int) ls []
  where go 0 rest acc = (P.Node r (reverse acc), rest)
        go i rest acc = let (c, rest') = tree f rest in go (i - 1) rest' (c : acc)
tree _ ls = error ("not a tree: " ++ show (take 1 ls))

force :: String -> IO (Either String String)
force s = either (Left . show . (show :: SomeException -> String)) (const (Right s))
  <$> try (evaluate (length s))

out :: String -> (a -> String) -> [a] -> IO ()
out tag f xs = force (show (length xs)) >>= either (\e -> putStrLn (tag ++ " ERROR " ++ e))
  (const (mapM_ (\x -> force (f x) >>= putStrLn . (tag ++) . either (" ERROR " ++) (' ' :)) xs))

codes :: String -> String
codes = unwords . map (show . ord)

nums :: [Integer] -> String
nums = unwords . map show

atom :: P.Atom -> String
atom (P.AStr s) = "AStr " ++ codes s
atom _ = "not AStr"

main :: IO ()
main = do
  [file] <- getArgs
  ls <- map words . lines <$> readFile file
  let lit = fst (tree (map (chr . fromInteger)) ls)
      cds = fst (tree id ls)
      absent = P.Absent :: P.Ptree String
  out "(a) lit" codes (P.lit_texts lit)
  out "(b) lit" show (P.lit_eq lit)
  out "(a) codes" nums (P.codes_texts cds)
  out "(b) codes" show (P.codes_eq cds)
  out "(c) lit" nums (P.lit_codes lit)
  out "(c) codes" nums (P.codes_codes cds)
  out "(d) lit" atom (P.lit_atoms lit)
  out "(d) codes" atom (P.codes_atoms cds)
  out "name_fun Node" id [P.name_fun lit]
  out "name_fun Absent" id [P.name_fun absent]
  out "name_case Node" id [P.name_case lit]
  out "name_case Absent" id [P.name_case absent]
  r <- try (putStrLn ("RAW " ++ unwords (P.lit_texts lit)))
  either (\e -> putStrLn ("RAW ERROR " ++ show (show (e :: SomeException)))) return r
