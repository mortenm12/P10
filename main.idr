import Control.Monad.State

infixr 5 :=
infixr 6 *=

--               T     | &T     | @T
data Ownership = Owned | Shared | Unique

||| Specifying what it means to be "not owned"
data NotOwned : Ownership -> Type where
    IsShared : NotOwned Shared
    IsUnique : NotOwned Unique

||| Proof that "NotOwned Owned" is nonsense
Uninhabited (NotOwned Owned) where
    uninhabited IsShared impossible
    uninhabited IsUnique impossible

||| Procedure for specifying whether or not a given ownership type is "not owned"
notOwned : (s : Ownership) -> Dec (NotOwned s)
notOwned Owned  = No absurd
notOwned Shared = Yes IsShared
notOwned Unique = Yes IsUnique

mutual
    data Stmt  : Type where 
        While  : Exp s  -> Scope -> Stmt
        If     : Exp s  -> Scope -> Scope -> Stmt
        (:=)   : String -> Exp s -> Stmt
        (*=) : {auto prf : NotOwned s} -> String -> Exp s -> Stmt -- {auto prf : ...} is an automatic proof for s
        Concat : Stmt   -> Stmt  -> Stmt 
        E      : Exp s  -> Stmt
        Return : Exp s  -> Stmt

    data Scope : Type where -- While (X "foo") [Return (X "foo")]
        Nil    : Scope
        (::)   : Stmt -> Scope -> Scope

    data Exp  : Ownership -> Type where 
        X     : String -> Exp Owned
        Sc    : Scope  -> Exp s
        Deref : String -> Exp s -- not sure
        At    : String -> Exp Unique
        Amp   : String -> Exp Shared
        (+)   : Exp s  -> Exp s' -> Exp Owned
        (-)   : Exp s  -> Exp s' -> Exp Owned
        (*)   : Exp s  -> Exp s' -> Exp Owned
        (/)   : Exp s  -> Exp s' -> Exp Owned
        Val   : Double -> Exp s

ProgramState : Type
ProgramState = State (List (String, String)) Int

mutual
    compileExp : Exp o -> Int

    compileScope : Scope -> Int
    compileScope Nil = 0
    compileScope (x :: xs) = (compile x) + (compileScope xs)

    assign : String -> Exp o -> Int
    assign str exp = ?help

    compile : Stmt -> Int
    compile (While e s) = if (compileExp e) >= 1 then compileScope s else 0
    compile (If e s1 s2) = if (compileExp e) >= 1 then compileScope s1 else compileScope s2
    compile ((:=) x e) = assign x e
