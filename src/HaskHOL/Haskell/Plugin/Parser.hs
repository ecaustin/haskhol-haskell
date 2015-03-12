{-|
  Module:    HaskHOL.Haskell.Plugin.Parser
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Haskell.Plugin.Parser where

import Control.Exception hiding (try)
import Control.Monad
import Control.Monad.Identity
import Data.Maybe
import Data.Text.Lazy hiding (map)
import qualified Data.Text.Lazy.IO as T

import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as P

-- Config File Parsing
parseFromFile :: SourceName -> Parsec Text () a -> IO (Either ParseError a) 
parseFromFile f p = liftM (runParser p () f) $ T.readFile f

language :: GenLanguageDef Text () Identity
language = P.LanguageDef 
    { P.commentStart = ""
    , P.commentEnd = ""
    , P.commentLine = ""
    , P.nestedComments = True
    , P.identStart = letter <|> oneOf "_$"
    , P.identLetter = alphaNum <|> oneOf "_'#$"
    , P.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , P.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , P.reservedOpNames = []
    , P.reservedNames = []
    , P.caseSensitive = True
    }

lexer :: P.GenTokenParser Text () Identity
lexer = P.makeTokenParser language

parens :: Parsec Text () a -> Parsec Text () a
parens = P.parens lexer

stringLiteral :: Parsec Text () String
stringLiteral = P.stringLiteral lexer

comma :: Parsec Text () String
comma = P.comma lexer

whiteSpace :: Parsec Text () ()
whiteSpace = P.whiteSpace lexer

pComment :: Parsec Text () (Maybe (Text, Text))
pComment =
    do void $ char '#'
       void $ manyTill anyChar newline
       return Nothing

pPair :: Parsec Text () (Maybe (Text, Text))
pPair = parens $
    do hsk <- stringLiteral
       void comma
       hol <- stringLiteral
       return (Just (pack hsk, pack hol))

parser :: Parsec Text () [Maybe (Text, Text)]
parser = sepBy1 (pComment <|> pPair) whiteSpace

parse :: SourceName -> IO [(Text, Text)]
parse f =
    do pairs <- parseFromFile f parser
       case pairs of
         Left err -> throwIO . userError $ show err
         Right res -> return $! catMaybes res
       

-- Option Parsing
pId :: Parsec Text () String
pId = P.identifier lexer

pOpt :: Parsec Text () (String, String)
pOpt =
    do key <- pId
       whiteSpace
       void $ char ':'
       whiteSpace
       val <- manyTill anyChar newline <?> "configuration setting"
       return (key, val)

optParser :: Parsec Text () [(String, String)]
optParser = sepBy1 pOpt whiteSpace

optParse :: SourceName -> IO [(String, String)]
optParse f =
    do opts <- parseFromFile f optParser
       case opts of
         Left err -> throwIO . userError $ show err
         Right res -> return res
