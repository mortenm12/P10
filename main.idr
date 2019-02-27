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