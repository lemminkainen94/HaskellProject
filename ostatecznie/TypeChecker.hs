module TypeChecker where

import AbsGrammar

import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import qualified Data.Map as M
import Data.Maybe


type Context = M.Map Variable Type
type ParamTypes = M.Map Ident FormalParameterList
type Eval a = ExceptT String (StateT (Context, ParamTypes) IO) a

addVar :: Variable -> Type -> (Context, ParamTypes) -> (Context, ParamTypes)
addVar var typ (cont, par) = (M.insert var typ cont, par)

lookupVar :: Variable -> Context -> Eval Type
lookupVar var con = do
  case var of
    FieldDes rId fId -> do
      RecordType tId <- lookupVar (Var rId) con
      case M.lookup (FieldDes tId fId) con of
        Just typ -> return $ typ
        Nothing -> throwError("The record "++(show tId)++" doesn't have a "++(show fId)++ " field")
    ArrayVariable id exp -> do
      arrTyp <- lookupVar (Var id) con
      expTyp <- inferExp exp con
      if expTyp /= IntType
        then
        throwError("In array "++(show id)++ " array index must be an int")
        else
        case arrTyp of
          IntArrayType _ -> return $ IntType
          LogicArrayType _ -> return $ LogicType
        
    _ -> case M.lookup var con of
      Just typ -> return $ typ
      Nothing -> throwError("Unbound variable "++(show var))

inferExp :: Exp -> Context -> Eval Type
inferExp (EInt i) con = return $ IntType
inferExp (ELogic l) con = return $ LogicType
inferExp (EVar v) con = lookupVar v con
inferExp (EFun id exps) con = do
  (_, fParam) <- get
  case M.lookup id fParam of
    Nothing -> throwError("Undefined function "++(show id))
    Just paramList -> do
      checkFunArgs paramList exps con
      lookupVar (Var id) con
    
inferExp (EMin exp) con = do
  typ <-  inferExp exp con
  case typ of
    IntType -> return $ IntType
    _ -> throwError("Type Error: " ++ (show exp) ++ " is not an integer")
inferExp (ENot exp) con = do
  typ <- inferExp exp con
  case typ of
    LogicType -> return $ LogicType
    _ -> throwError("Type Error: " ++ (show exp) ++ " is not a logical value")

inferExp (EOr exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (LogicType, LogicType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (EAnd exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (LogicType, LogicType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")

inferExp (ELess exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (EGreater exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (ELessEqual exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (EGreaterEqual exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (EEqual exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    (LogicType, LogicType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")
inferExp (ENonEqual exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ LogicType
    (LogicType, LogicType) -> return $ LogicType
    _ -> throwError("Type Error: invalid logical expression")

inferExp (EAdd exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ IntType
    _ -> throwError("Error: invalid integer expression")
inferExp (ESub exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ IntType
    _ -> throwError("Error: invalid integer expression")
inferExp (EMul exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ IntType
    _ -> throwError("Error: invalid integer expression")
inferExp (EDiv exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ IntType
    _ -> throwError("Error: invalid integer expression")
inferExp (EMod exp1 exp2) con = do
  t1 <- inferExp exp1 con
  t2 <- inferExp exp2 con
  case (t1, t2) of
    (IntType, IntType) -> return $ IntType
    _ -> throwError("Error: invalid integer expression")

checkStmt :: Statement -> (Context, ParamTypes) -> Eval ()
checkStmt (ExpStmt exp) state = return ()
checkStmt (PrintStmt exp) state = return ()
checkStmt (AssignStmt var exp) (con, _) = do
  varType <- lookupVar var con
  expType <- inferExp exp con
  case (varType, expType) of
    (IntType, IntType) -> return ()
    (LogicType, LogicType) -> return ()
    (IntArrayType i, IntArrayType j) -> if (i==j)
      then return ()
      else throwError("Error: assignment of array of size "++(show j)++" to array of size "++(show i))
    (LogicArrayType i, LogicArrayType j) -> if (i==j)
      then return ()
      else throwError("Error: assignment of array of size "++(show j)++" to array of size "++(show i))
    (RecordType id1, RecordType id2) -> if (id1==id2)
      then return ()
      else throwError("Error: cannot assign record "++(show id2)++" to record "++(show id1))
    _ -> throwError("Error: cannot assign "++(show exp)++" to "++(show var))

checkStmt (IfStmt exp _) (con, _) = do
  expType <- inferExp exp con
  case (expType) of
    LogicType -> return ()
    _ -> throwError("Type Error: incorrect logical expression"++(show exp)++" in if statement")
checkStmt (IfElseStmt exp _ _) (con, _) = do
  expType <- inferExp exp con
  case (expType) of
    LogicType -> return ()
    _ -> throwError("Type Error: incorrect logical expression"++(show exp)++" in if-else statement")
checkStmt (WhileStmt exp _) (con, _) = do
  expType <- inferExp exp con
  case (expType) of
    LogicType -> return ()
    _ -> throwError("Type Error: incorrect logical expression"++(show exp)++" in while statement")

checkStmt (ForToStmt id exp1 exp2 _) (con, _) = do
  idType <- lookupVar (Var id) con
  exp1Type <- inferExp exp1 con
  exp2Type <- inferExp exp2 con
  case (idType, exp1Type, exp2Type) of
    (IntType, IntType, IntType) -> return ()
    _ -> throwError("Type error: incorrect 'for' statement")
checkStmt (ForDowntoStmt id exp1 exp2 _) (con, _) = do
  idType <- lookupVar (Var id) con
  exp1Type <- inferExp exp1 con
  exp2Type <- inferExp exp2 con
  case (idType, exp1Type, exp2Type) of
    (IntType, IntType, IntType) -> return ()
    _ -> throwError("Type error: incorrect 'for' statement")

checkFunArgs :: FormalParameterList -> [Exp] -> Context -> Eval ()
checkFunArgs (FormalParamList []) [] _ = return ()
checkFunArgs (FormalParamList _) []  _ = throwError("Wrong number of arguments")
checkFunArgs (FormalParamList []) _  _ = throwError("Wrong number of arguments")
checkFunArgs (FormalParamList (p:ps)) (exp:exps) con = case p of
  ValParamSect pTyp pId -> do
    eTyp <- inferExp exp con
    if (pTyp == eTyp)
      then checkFunArgs (FormalParamList ps) exps con
      else throwError("Wrong argument type: formal parameter if of type: "++(show pTyp)++" actual parameter is of type: "++(show eTyp))
  VarParamSect pTyp pId -> case exp of
    (EVar _) -> do
      eTyp <- inferExp exp con
      if (pTyp == eTyp)
        then checkFunArgs (FormalParamList ps) exps con
        else throwError("Wrong argument type: formal parameter if of type: "++(show pTyp)++" actual parameter is of type: "++(show eTyp))
    _ -> throwError("Parameter called by reference must be a variable")

addFieldIdType :: Type -> Ident -> Ident -> Eval ()
addFieldIdType typ tid id = modify (addVar (FieldDes tid id) typ)

checkField :: Ident -> Field -> Eval ()
checkField tid field = case field of
  IntRecFld idsi -> mapM_ (addFieldIdType IntType tid) idsi
  LogicRecFld idsl -> mapM_ (addFieldIdType LogicType tid) idsl

checkRecDef :: RecordDefinition -> Eval ()
checkRecDef recDef = let (RecDef id fields) = recDef in
  do
    modify (addVar (Var id) (RecordType id))
    mapM_ (checkField id) fields

checkTypeDefPart :: TypeDefinitionPart -> Eval ()
checkTypeDefPart typeDefPart = case typeDefPart of
  TypeDefPartEmpty -> return ()
  TypeDefPart recDefs -> mapM_ checkRecDef recDefs

checkVarDecl :: VariableDeclaration -> Context -> Eval Context
checkVarDecl varDecl con = let (VarDecl typ id) = varDecl in 
  case typ of
    VoidType -> throwError("Void type restricted to functions")
    _ -> do
      case M.lookup (Var id) con of
        Just (RecordType tId) ->
          throwError("Illegal var name: "++(show id)++" is a record type name")
        _ -> return $ M.insert (Var id) typ con


checkVarDeclPart :: VariableDeclarationPart-> Context -> Eval Context
checkVarDeclPart varDeclPart con = case varDeclPart of
  VarDeclPartEmpty -> return $ con
  VarDeclPart varDecls -> case varDecls of
    [] -> return $ con
    (v:vs) -> do
      newCon <- checkVarDecl v con
      checkVarDeclPart (VarDeclPart vs) newCon

paramToVarDecl :: FormalParameterSection -> VariableDeclaration
paramToVarDecl fParam = case fParam of
  VarParamSect typ id -> VarDecl typ id
  ValParamSect typ id -> VarDecl typ id

checkFormalParamList :: FormalParameterList -> Context -> Eval Context
checkFormalParamList (FormalParamList fParams) fCon =
  checkVarDeclPart (VarDeclPart (map paramToVarDecl fParams)) fCon 

checkFunHead :: FunctionHeading -> Eval Context
checkFunHead (FunHead id fParamList typ) = do
  modify (addVar (Var id) typ)
  (con, fParam) <- get
  put (con, (M.insert id fParamList fParam))
  checkFormalParamList fParamList con

checkRetStmt :: Type -> ReturnStatement -> Context -> Eval ()
checkRetStmt fType retStmt con = case retStmt of
  RetStmtEmpty -> if (fType == VoidType)
    then return ()
    else throwError("Missing value in return statement of function of type "++(show fType))
  RetStmt exp -> do
    retType <- inferExp exp con
    if (retType == fType)
      then return ()
      else throwError("Function and return types not matching")

checkFunStmtPart :: Type -> FunctionStatementPart -> Context -> Eval ()
checkFunStmtPart fType (FunStmtPart stmts retStmt) con = do
  (_, fParam) <- get
  checkStmtPart (StmtPart stmts) (con, fParam)
  checkRetStmt fType retStmt con

checkFunBody :: Type -> FunctionBody -> Context -> Eval ()
checkFunBody fType (FunBody decls stmts) con = do
  newCon <- checkVarDeclPart decls con
  checkFunStmtPart fType stmts newCon

checkFunDecl :: FunctionDeclaration -> Eval ()
checkFunDecl (FunDecl fHead fBody) = let (FunHead _ _ fType) = fHead in
  do
    con <- checkFunHead fHead
    checkFunBody fType fBody con

checkFunDeclPart :: FunctionDeclarationPart -> Eval ()
checkFunDeclPart (FunDeclPart funDecls) = mapM_ checkFunDecl funDecls

checkStmtPart :: StatementPart -> (Context, ParamTypes) -> Eval ()
checkStmtPart (StmtPart stmts) state = case stmts of
  [] -> return ()
  (s:ss) -> do
    checkStmt s state
    checkStmtPart (StmtPart ss) state

checkProgram :: Program -> Eval ()
checkProgram (Prog progHead (DeclPart typeDef varDecl funDecl) stmtPart) = do
  checkTypeDefPart typeDef
  (c, f) <- get
  con <- checkVarDeclPart varDecl c
  put (con, f)
  checkFunDeclPart funDecl
  state <- get
  checkStmtPart stmtPart state

runTypeChecker :: (Context, ParamTypes) -> Eval a -> IO (Either String a, (Context, ParamTypes))
runTypeChecker state ev = runStateT (runExceptT ev) state
