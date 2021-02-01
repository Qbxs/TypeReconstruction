module Parser ( parseTerm
              , parseStmt
              , Stmt(..)
              ) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Char (alphaNum)
import TypeReconstruction (Term(..))

data Stmt
   = Check Term
   | Constraints Term
   | Help
   | Quit

parseStmt :: String -> Either ParseError Stmt
parseStmt = parse stmt "ParseError:"

stmt :: Parser Stmt
stmt = choice [ try quit
              , try help
              , try constraints
              , check
              ]

check :: Parser Stmt
check = Check <$> term

constraints :: Parser Stmt
constraints = (string ":c" <|> string ":constraints") >> spaces >> Constraints <$> term

help :: Parser Stmt
help = (string ":h" <|> string ":help") >> return Help

quit :: Parser Stmt
quit = (string ":q" <|> string ":quit") >> return Quit


parseTerm :: String -> Either ParseError Term
parseTerm = parse term "ParseError:"


lambda :: Parser Char
lambda = char '\\' <|> char '\955'

firstLower :: Parser String
firstLower = lower >>= \c -> many alphaNum >>= \str -> return $ c:str


term :: Parser Term
term = choice [ try abstraction
              , try application
              , try addition
              , try number
              , variable
              ]

variable :: Parser Term
variable = Var <$> firstLower

number :: Parser Term
number = Nat . read <$> many1 digit

abstraction :: Parser Term
abstraction = do
  lambda
  str <- firstLower
  char '.'
  spaces
  t <- term
  return $ Lam str t

application :: Parser Term
application = do
  char '('
  t1 <- term
  many1 space
  t2 <- term
  char ')'
  return $ App t1 t2

addition :: Parser Term
addition = do
  char '('
  t1 <- term
  spaces
  char '+'
  spaces
  t2 <- term
  char ')'
  return $ Add t1 t2
