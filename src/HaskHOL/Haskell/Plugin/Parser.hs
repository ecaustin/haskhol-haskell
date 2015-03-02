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
import Data.Text hiding (map)
import qualified Data.Text.IO as T

import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as P

-- Config File Parsing
language :: GenLanguageDef Text () Identity
language = P.LanguageDef 
    { P.commentStart = ""
    , P.commentEnd = ""
    , P.commentLine = ""
    , P.nestedComments = True
    , P.identStart = letter <|> char '_'
    , P.identLetter = alphaNum <|> oneOf "_'#"
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
    do pairs <- parseFromFile parser
       case pairs of
         Left err -> throwIO . userError $ show err
         Right res -> return $! catMaybes res
  where parseFromFile :: Parsec Text () a -> IO (Either ParseError a) 
        parseFromFile p = liftM (runParser p () f) $ T.readFile f
       

-- Option Parsing
language' :: LanguageDef ()
language' = emptyDef

lexer' :: P.TokenParser ()
lexer' = P.makeTokenParser language'

identifier :: Parsec String () String
identifier = P.identifier lexer'

dot :: Parsec String () String
dot = P.dot lexer'

pId :: Parsec String () String
pId = 
    do ids <- identifier `sepBy1` dot
       case ids of
         [x] -> return x
         [x, y] -> return $! x ++ "." ++ y
         _ -> fail "optParse: bad key value pair."

pEq :: Parsec String () (String, String)
pEq =
    do key <- pId
       void $ char '='
       val <- pId <?> "configuration setting"
       return (key, val)

optParse :: [String] -> IO (Maybe String, Maybe String, Maybe String)
optParse opts =
    case mapM (runParser pEq () undefined) opts of
      Left err -> throwIO . userError $ show err
      Right opts' -> return
        (lookup "ctxt" opts', lookup "types" opts', lookup "terms" opts')
