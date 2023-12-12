module MinHS.Pretty where
import MinHS.Syntax
import MinHS.TypeChecker

import Prettyprinter as L
import Prettyprinter.Render.Terminal

prettyList' :: (a -> Doc AnsiStyle) -> [a] -> Doc AnsiStyle
prettyList' f = align . list . map f

primop, keyword, datacon, typecon, symbol, err :: String -> Doc AnsiStyle
numeric :: Integer -> Doc AnsiStyle
primop  = annotate (colorDull Yellow) . pretty
keyword = annotate bold               . pretty
datacon = annotate (colorDull Green)  . pretty
typecon = annotate (color Blue)       . pretty
numeric = annotate (colorDull Cyan)   . pretty
symbol  = annotate (color Magenta)    . pretty
err     = annotate (color Red)        . pretty

prettyBind :: Bind -> Doc AnsiStyle
prettyBind (Bind n ty ps expr) =
  pretty n <+> symbol "::" <+> prettyType ty <+> params (symbol "=" <+> prettyExp expr)
    where params = if null ps then id else (hsep (map pretty ps) <+>)

prettyBinds :: [Bind] -> Doc AnsiStyle
prettyBinds = vcat . map (<> semi) . map prettyBind

prettyType :: Type -> Doc AnsiStyle
prettyType = go2
  where
    go1 :: Type -> Doc AnsiStyle
    go1 (a `Arrow` b) = go2 a <+> symbol "->" <+> go1 b
    go1 (TypeApp (TypeCon List) b) = annotate (color Blue) lbracket <> go1 b <> annotate (color Blue) rbracket
    go1 (TypeApp a b) = go1 a <+> go3 b
    go1 (TypeCon Unit) = typecon "()"
    go1 (TypeCon x)    = typecon (show x)
    go2 :: Type -> Doc AnsiStyle
    go2 t@(_ `Arrow` _) = parens (go1 t)
    go2 t = go1 t
    go3 :: Type -> Doc AnsiStyle
    go3 t@(TypeApp _ _) = parens (go1 t)
    go3 t = go2 t

prettyOp :: Op -> Doc AnsiStyle
prettyOp Add  = primop "+"
prettyOp Sub  = primop "-"
prettyOp Mul  = primop "*"
prettyOp Quot = primop "/"
prettyOp Rem  = primop "%"
prettyOp Neg  = primop "-"
prettyOp Gt   = primop ">"
prettyOp Ge   = primop ">="
prettyOp Lt   = primop "<"
prettyOp Le   = primop "<="
prettyOp Eq   = primop "=="
prettyOp Ne   = primop "/="
prettyOp Head = primop "head"
prettyOp Null = primop "null"
prettyOp Tail = primop "tail"

prettyExp :: Exp -> Doc AnsiStyle
prettyExp expr = case expr of
  Var i -> pretty i
  App (Prim Neg) e2 -> parens (pretty "-" <+> prettyExpParens e2)
  Prim Head -> pretty "head"
  Prim Tail -> pretty "tail"
  Prim o -> parens (prettyOp o)
  Con i -> datacon i
  Num i -> numeric i
  App e1 e2 -> prettyExp e1 <+> prettyExpParens e2
  If c t e ->
    keyword "if" <+> align (prettyExp c
                            <--> keyword "then" <+> prettyExp t
                            <--> keyword "else" <+> prettyExp e)
  Let bs e -> align (keyword "let" <+> align (prettyBinds bs) <--> keyword "in" <+> prettyExp e)
  Recfun b -> parens (keyword "recfun" <+> prettyBind b)
  Letrec bs e -> align (keyword "letrec" <+> align (prettyBinds bs) <--> keyword "in" <+> prettyExp e)
  where
    prettyExpParens :: Exp -> Doc AnsiStyle
    prettyExpParens t@(App _ _) = parens (prettyExp t)
    prettyExpParens t           = prettyExp t

prettyTypeError :: TypeError -> Doc AnsiStyle
prettyTypeError terr = case terr of
  TypeMismatch t1 t2 e ->
    err "Type mismatch:"
    <--> indent 3 (prettyType t1)
    <--> err "is not"
    <--> indent 3 (prettyType t2)
    <--> err "in expression"
    <--> indent 3 (prettyExp e)
  TypeShouldBeFunction ty b ->
    err "Parameter list suggests this atomic type"
    <--> indent 3 (prettyType ty)
    <--> err "to be a function, in binding:"
    <--> indent 3 (prettyBind b)
  FunctionTypeExpected e t ->
    err "Function application must be performed on a function, but this:"
    <--> indent 3 (prettyExp e)
    <--> err "is of type" <+> prettyType t
  NoSuchVariable x ->
    err "Variable" <+> pretty x <+> err "not in scope."
  NoSuchConstructor x ->
    err "Constructor" <+> pretty x <+> err "not in scope."
  TypeConstructorSaturated t _k ->
    err "Expected" <+> prettyType t <+> err "to be a type constructor, but it is an atomic type."
  KindMismatch _k1 _k2 t ->
    err "Type term" <+> prettyType t <+> err "is not valid."

(<-->) :: Doc ann -> Doc ann -> Doc ann
a <--> b = a <> line <> b
