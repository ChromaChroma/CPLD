import MinHS.Parse
import MinHS.Syntax
import MinHS.TypeChecker
import MinHS.Evaluator
import MinHS.Pretty
import Control.Monad
import Options.Applicative.Types
import Options.Applicative
import Prettyprinter (Doc, unAnnotate)
import Prettyprinter.Render.Terminal (AnsiStyle, putDoc)

type Action a b = a -> Either (IO ()) b

main :: IO ()
main = execParser argsInfo >>= main'
  where main' (pipeline, outfilter, file) = (pipeline outfilter <$> readFile file) >>= either id id

        argsInfo = info (helper <*> args)
                    (fullDesc <> progDesc "A interpreter for a small functional language"
                              <> header "MinHS - Concepts of Program Design")

        args =  (,,) <$> option readAction ( long "dump"
                               <> metavar "STAGE"
                               <> value evaluatorAction
                               <> help "stage after which to dump the current state. \n                           [parser,parser-raw,typechecker,evaluator]")
                     <*> flag id unAnnotate (long "no-colour"
                                          <> help "do not use colour when pretty printing")
                     <*> argument str (metavar "FILE")

        readAction :: ReadM ((Doc AnsiStyle -> Doc AnsiStyle) -> Action String (IO ()))
        readAction = readerAsk >>= \x -> case x of
            "parser"      -> return $ \f -> parser >=> printer prettyBinds f
            "parser-raw"  -> return $ \_ -> parser >=> rawPrinter
            "typechecker" -> return $ \f -> parser >=> typechecker f >=> printer prettyBinds f
            "evaluator"   -> return $ evaluatorAction
            _             -> readerAbort (ShowHelpText Nothing)

        evaluatorAction :: (Doc AnsiStyle -> Doc AnsiStyle) -> Action String (IO ())
        evaluatorAction f = parser >=> typechecker f >=> evaluator >=> printer prettyValue f

        parser :: Action String Program
        parser = either (Left . putStrLn . show) Right . parseProgram ""

        typechecker :: (Doc AnsiStyle -> Doc AnsiStyle) -> Action Program Program
        typechecker f p | Just v <- typecheck p = Left . (>> putStrLn "") . putDoc . f . prettyTypeError $ v
                        | otherwise             = Right $ p

        evaluator p = Right $ evaluate p

        rawPrinter :: (Show a) => Action a (IO ())
        rawPrinter = Right . putStrLn . show

        printer :: (a -> Doc AnsiStyle) -> (Doc AnsiStyle -> Doc AnsiStyle) -> Action a (IO ())
        printer pr outfilter = Right . (>> putStrLn "") . putDoc . outfilter . pr
