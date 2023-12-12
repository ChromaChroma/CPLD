module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Prettyprinter as PP
import Prettyprinter.Render.Terminal (AnsiStyle)
import Debug.Trace
import Text.Show.Functions ()

type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           -- Add other variants as needed
           deriving (Show, Read)

prettyValue :: Value -> PP.Doc AnsiStyle
prettyValue (I i) = numeric i
prettyValue (B b) = datacon (show b)
prettyValue (Nil) = datacon "Nil"
prettyValue (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> prettyValue v)



data MachineState  -- add the definition



-- do not change this definition
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE e
evaluate _ = error "Input program did not have exactly one binding"

-- do not change this definition
evalE :: Exp -> Value
evalE expr = loop (msInitialState expr)
  where 
    loop ms = -- (trace "debug message") $  -- uncomment this line and pretty print the machine state/parts of it to
                                            -- observe the machine states
             if (msInFinalState newMsState)
                then msGetValue newMsState
                else loop newMsState
              where
                 newMsState = msStep ms

msInitialState :: Exp -> MachineState
msInitialState _ = error "implement me!"

-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState _ = error "implement me!"

-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue _ = error "implement me!"
  
msStep :: MachineState -> MachineState
msStep _ = error "implement me!"
