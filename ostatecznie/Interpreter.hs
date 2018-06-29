{-# LANGUAGE TemplateHaskell #-}
module Interpreter where

import AbsGrammar

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Data.Map as M
import Data.Maybe


data Value =
  IntVal Integer
  | LogicVal Bool
  | ArrayVal (M.Map Integer Integer)
  | RecordVal (M.Map Ident Integer)
  | FunVal Type FormalParameterList FunctionBody Env
  | VoidVal

type Env = M.Map Variable Integer
type Store = M.Map Integer Value
type Eval a = ExceptT String (StateT (Integer, Store)  IO) a

instance Show Value where
  show val = case val of
    IntVal int -> show int
    LogicVal log -> show log

getLoc :: Env -> Variable -> Eval Integer
getLoc env var = case var of
  Var id -> case M.lookup var env of
    Just i -> return $ i
    Nothing -> throwError("Unbound variable " ++ (show var))
  ArrayVariable id exp -> do
    ArrayVal map <- getVar env (Var id)
    IntVal index <- eval exp env
    case M.lookup index map of
      Just mLoc -> return $ mLoc
      Nothing -> throwError("Index out of bounds in array: "++(show id))
  FieldDes rId fId -> do
    RecordVal map <- getVar env (Var rId)
    case M.lookup fId map of
      Just mLoc -> return $ mLoc
      Nothing -> throwError("Field "++(show fId)++" does not exist in record "++(show rId))

getVar :: Env -> Variable -> Eval Value
getVar env var = do
  (next, store) <- get
  case var of
    Var id -> do
      i <- getLoc env var
      let Just val = M.lookup i store in return $ val 
    ArrayVariable id exp -> do
      ArrayVal map <- getVar env (Var id)
      IntVal index <- eval exp env
      case M.lookup index map of
        Just mLoc -> let Just mVal = M.lookup mLoc store in return $ mVal
        Nothing -> throwError("Index out of bounds in array: "++(show id))
    FieldDes rId fId -> do
      RecordVal map <- getVar env (Var rId)
      case M.lookup fId map of
        Just mLoc -> let Just mVal = M.lookup mLoc store in return $ mVal
        Nothing -> throwError("Field "++(show fId)++" does not exist in record "++(show rId))

evalLogical :: Logical -> Eval Bool
evalLogical (Logical "true") = return True
evalLogical (Logical "false") = return False

eval :: Exp -> Env -> Eval Value
eval (EInt i) env = return $ IntVal i
eval (ELogic l) env = do
  val <- evalLogical l
  return $ LogicVal val
eval (EVar v) env = do
  getVar env v
eval (EFun id exps) env = do
  (FunVal fType params (FunBody vDecls fStmts) fEnv) <- getVar env (Var id)
  fVarEnv <- interpretVarDeclPart vDecls fEnv
  fParEnv <- interpretFormalParamList params fVarEnv
  fArgEnv <- interpretFunCallArgs params exps fParEnv env
  interpretFunStmtPart fStmts fArgEnv

eval (EMin exp) env = do
  e <- eval exp env
  let IntVal i = e in
    return $ IntVal (-i)
eval (ENot exp) env = do
  e <- eval exp env
  let LogicVal l = e in
    return $ LogicVal (not l)
    
eval (EOr exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (LogicVal l1, LogicVal l2) -> return $ LogicVal(l1 || l2)
    _ -> throwError("Error: invalid logical expression")
eval (EAnd exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (LogicVal l1, LogicVal l2) -> return $ LogicVal(l1 && l2)
    _ -> throwError("Error: invalid logical expression")

eval (ELess exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 < i2)
    _ -> throwError("Error: invalid integer expression")
eval (EGreater exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 > i2)
    _ -> throwError("Error: invalid integer expression")
eval (ELessEqual exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 <= i2)
    _ -> throwError("Error: invalid integer expression")
eval (EGreaterEqual exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 >= i2)
    _ -> throwError("Error: invalid integer expression")
eval (EEqual exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 == i2)
    (LogicVal l1, LogicVal l2) -> return $ LogicVal(l1 == l2)
    _ -> throwError("Error: invalid integer expression")
eval (ENonEqual exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ LogicVal(i1 /= i2)
    (LogicVal l1, LogicVal l2) -> return $ LogicVal(l1 /= l2)
    _ -> throwError("Error: invalid integer expression")

eval (EAdd exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ IntVal(i1 + i2)
    _ -> throwError("Error: invalid integer expression")
eval (ESub exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ IntVal(i1 - i2)
    _ -> throwError("Error: invalid integer expression")
eval (EMul exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> return $ IntVal(i1 * i2)
    _ -> throwError("Error: invalid integer expression")
eval (EDiv exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> case i2 of
      0 -> throwError("Error: division by zero!")
      _ -> return $ IntVal(i1 `div` i2)
    _ -> throwError("Error: invalid integer expression")
eval (EMod exp1 exp2) env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case (e1, e2) of
    (IntVal i1, IntVal i2) -> case i2 of
      0 -> throwError("Error: modulo zero!")
      _ -> return $ IntVal(i1 `mod` i2)
    _ -> throwError("Error: invalid integer expression")

exec :: Statement -> Env -> Eval ()
exec (ExpStmt exp) env = do
  eval exp env
  return ()
exec (PrintStmt exp) env = do
  val <- eval exp env
  liftIO $ putStrLn $ show $ val
  
exec (AssignStmt var exp) env = do
  val <- eval exp env
  (next, store) <- get
  case var of
    Var _ -> do
      vLoc <- getLoc env var
      case val of
        IntVal int -> do
          let newStore = M.insert vLoc (IntVal int) store in
            put (next, newStore) 
        LogicVal log -> do
          let newStore = M.insert vLoc (LogicVal log) store in
            put (next, newStore)
        _ -> do
          map <- eval exp env
          let newStore =  M.insert vLoc map store in
            put (next, newStore)
    ArrayVariable id indExp -> do
      _ <- getVar env var 
      ArrayVal map <- eval (EVar (Var id)) env
      IntVal index <- eval indExp env
      let Just vLoc = M.lookup index map in
        let newStore = M.insert vLoc val store in
          put (next, newStore)
    FieldDes rId fId -> do
      _ <- getVar env var
      RecordVal map <- eval (EVar (Var rId)) env
      let Just vLoc = M.lookup fId map in
        let newStore = M.insert vLoc val store in
          put (next, newStore)

exec (IfStmt exp stmts) env = do
  val <- eval exp env
  case val of
    LogicVal log -> case log of
      True -> interpretStmtPart stmts env
      False -> return ()
    _ -> throwError("Invalid logical expression")

exec (IfElseStmt exp stmts1 stmts2) env = do
  val <- eval exp env
  case val of
    LogicVal log -> case log of 
      True -> interpretStmtPart stmts1 env
      False -> interpretStmtPart stmts2 env
    _ -> throwError("Invalid logical expression")

exec (WhileStmt exp stmts) env = do
  val <- eval exp env
  case val of
    LogicVal log -> case log of
      True -> do
        interpretStmtPart stmts env
        exec (WhileStmt exp stmts) env
      False -> return ()
    _ -> throwError("Invalid logical expression")

exec (ForToStmt id exp1 exp2 stmts) env = do
  exec (AssignStmt (Var id) exp1) env
  less <- eval (ELess (EVar (Var id)) exp2) env
  case less of
    LogicVal True -> do
      interpretStmtPart stmts env
      idVal <- eval (EVar (Var id)) env
      let IntVal i = idVal in
        exec (ForToStmt id (EInt (i+1)) exp2 stmts) env
    LogicVal False -> return ()
    _ -> throwError("Error in for: incorrect expression")

exec (ForDowntoStmt id exp1 exp2 stmts) env = do
  exec (AssignStmt (Var id) exp1) env
  less <- eval (EGreater (EVar (Var id)) exp2) env
  case less of
    LogicVal True -> do
      interpretStmtPart stmts env
      idVal <- eval (EVar (Var id)) env
      let IntVal i = idVal in
        exec (ForDowntoStmt id (EInt (i-1)) exp2 stmts) env
    LogicVal False -> return ()
    _ -> throwError("Error in for: incorrect expression")
  
interpretFunCallArgs :: FormalParameterList -> [Exp] -> Env -> Env -> Eval Env
interpretFunCallArgs (FormalParamList []) [] fEnv env = return $ fEnv
interpretFunCallArgs (FormalParamList (p:ps)) (exp:exps) fEnv env = do
  expVal <- eval exp env
  (n, store) <- get
  case p of
    ValParamSect pType pId -> do
      pLoc <- getLoc fEnv (Var pId)
      let newStore = M.insert pLoc expVal store in
        put (n, newStore)
      interpretFunCallArgs (FormalParamList ps) exps fEnv env
    VarParamSect pType pId -> let EVar v = exp in
      do
        vLoc <- getLoc env v
        let newEnv = M.insert (Var pId) vLoc fEnv in
          interpretFunCallArgs (FormalParamList ps) exps newEnv env

interpretFieldIds :: Type -> Integer -> [Ident] -> Eval ()
interpretFieldIds typ n fIds = case fIds of
  [] -> return ()
  (f:fs) -> do
    (next, store) <- get
    case M.lookup n store of
      Just (RecordVal map) ->
        case typ of
          IntType ->
            let newStore = M.insert next (IntVal 0) store in
              let recStore = M.insert n (RecordVal (M.insert f next map)) newStore in
                do
                  put (next + 1, recStore)
                  interpretFieldIds typ n fs
          LogicType ->
            let newStore = M.insert next (LogicVal False) store in
              let recStore = M.insert n (RecordVal (M.insert f next map)) newStore in
                do
                  put(next + 1, recStore)
                  interpretFieldIds typ n fs
      Nothing -> throwError("Type construction error")
      
interpretFields :: Integer -> [Field] -> Eval ()
interpretFields n [] = return $ ()
interpretFields n (field:fields) = case field of
  IntRecFld idsI -> do
    interpretFieldIds IntType n idsI
    interpretFields n fields
  LogicRecFld idsL -> do
    interpretFieldIds LogicType n idsL
    interpretFields n fields

interpretRecDef :: RecordDefinition -> Env -> Eval Env
interpretRecDef recDef env = let (RecDef id fields) = recDef in
  do
    (n, store) <- get
    let storeType = M.insert n (RecordVal M.empty) store in
      do
        put (n+1, storeType)
        interpretFields n fields
        let newEnv = M.insert (Var id) n env in
          return $ newEnv

interpretTypeDefPart ::TypeDefinitionPart -> Env -> Eval Env
interpretTypeDefPart typeDefPart env = case typeDefPart of
  TypeDefPartEmpty -> return $ env
  TypeDefPart recDefs -> case recDefs of
    [] -> return $ env
    (rDef:rDefs) -> do
      newEnv <- interpretRecDef rDef env
      interpretTypeDefPart (TypeDefPart rDefs) newEnv

insertArrayVariables :: Integer -> Value -> [Integer] -> Eval ()
insertArrayVariables loc val inds = case inds of
  [] -> return ()
  (i:is) -> do
    (next, store) <- get
    case M.lookup loc store of
      Just (ArrayVal map) -> do
        let newStore = M.insert next (IntVal 0) store in
          let arrStore = M.insert loc (ArrayVal (M.insert i next map)) newStore in
            do
              put (next+1, arrStore)
              insertArrayVariables loc val is
      _ -> throwError("Array not found")
  
interpretVarDecl :: VariableDeclaration -> Env -> Eval Env
interpretVarDecl varDecl env = do
  (next, store) <- get
  let (VarDecl typ id) = varDecl in
    let newEnv = M.insert (Var id) next env in
      do
        case typ of
          IntType -> let newStore = M.insert next (IntVal 0) store in
            put (next + 1, newStore)
          LogicType -> let newStore = M.insert next (LogicVal False) store in
            put (next + 1, newStore)
          IntArrayType i -> let storeArray = M.insert next (ArrayVal M.empty) store in
            do
              put (next+1, storeArray)
              insertArrayVariables next (IntVal 0) [0..i-1]
          LogicArrayType i -> let storeArray = M.insert next (ArrayVal M.empty) store in
            do
              put (next+1, storeArray)
              insertArrayVariables next (LogicVal False) [0..i-1]
          RecordType rId -> do
            recDefVal <- getVar env (Var rId)
            let newStore = M.insert next recDefVal store in
              put (next + 1, newStore)
        return $ newEnv
       
interpretVarDeclPart :: VariableDeclarationPart -> Env -> Eval Env
interpretVarDeclPart varDeclPart env = case varDeclPart of
  VarDeclPartEmpty -> return $ env
  VarDeclPart varDecls -> case varDecls of
    [] -> return $ env
    (v:vs) -> do
      newEnv <- interpretVarDecl v env
      interpretVarDeclPart (VarDeclPart vs) newEnv

paramToVarDecl :: FormalParameterSection -> VariableDeclaration
paramToVarDecl fParam = case fParam of
  VarParamSect typ id -> VarDecl typ id
  ValParamSect typ id -> VarDecl typ id

interpretFormalParamList :: FormalParameterList -> Env -> Eval Env
interpretFormalParamList (FormalParamList fParams) env =
  interpretVarDeclPart (VarDeclPart (map paramToVarDecl fParams)) env

interpretRetStmt :: ReturnStatement -> Env -> Eval Value
interpretRetStmt retStmt env = case retStmt of
  RetStmtEmpty -> return $ VoidVal
  RetStmt exp -> do
    retVal <- eval exp env
    return $ retVal

interpretFunStmtPart :: FunctionStatementPart -> Env -> Eval Value
interpretFunStmtPart (FunStmtPart stmts retStmt) env = do
  interpretStmtPart stmts env
  interpretRetStmt retStmt env

interpretFunDecl :: FunctionDeclaration -> Env -> Eval Env
interpretFunDecl (FunDecl fHead fBody) env = do
  (next, store) <- get
  let (FunHead id fParamList typ) = fHead in
    do
      let recEnv = M.insert (Var id) next env in
        let (FunBody vDecls fStmts) = fBody in
          let newStore = M.insert next (FunVal typ fParamList fBody recEnv) store in
            put (next + 1, newStore)
      return $ M.insert (Var id) next env
       
interpretFunDeclPart :: FunctionDeclarationPart -> Env -> Eval Env
interpretFunDeclPart (FunDeclPart []) env = return $ env
interpretFunDeclPart (FunDeclPart (fDecl:fDecls)) env = do
  newEnv <- interpretFunDecl fDecl env
  interpretFunDeclPart (FunDeclPart fDecls) newEnv

interpretStmtPart :: [Statement] -> Env -> Eval ()
interpretStmtPart [] env = return ()
interpretStmtPart (stmt:stmts) env = do
  exec stmt env
  interpretStmtPart stmts env

interpretProgram :: Program -> Eval ()
interpretProgram (Prog progHead (DeclPart typeDef varDecl funDecl) stmtPart) = do
  env <- interpretTypeDefPart typeDef M.empty
  varEnv <- interpretVarDeclPart varDecl env
  varFunEnv <- interpretFunDeclPart funDecl varEnv
  let StmtPart stmts = stmtPart in
    interpretStmtPart stmts varFunEnv
  
runInterpreter :: (Integer,Store) -> Eval a -> IO (Either String a, (Integer, Store))
runInterpreter env ev = runStateT (runExceptT ev) env
