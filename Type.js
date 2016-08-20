  // All js boys

  // Type = TypeVar
  //      | Literal
  //      | Function this next

  // Returns a new set with distinct elements from s1 and s2
  Set.union = function(s1, s2){
    s = new Set([]);
    s1.forEach(function(i){
      s.add(i);
    });
    s2.forEach(function(i){
      s.add(i);
    });
    return s;
  }

  // if next then name is type and next is a type
  Type = function(base, next){
    this.base = base;
    this.next = next;
  }

  Type.prototype.isTypeVar = function(){
    return !this.isFunction() && this.base.startsWith("_POLY_");
  }

  Type.prototype.isLiteral = function(){
    return !this.isTypeVar();
  }

  Type.prototype.getLiteral = function(){
    if(!this.isLiteral()) 
      // We error in order to avoid mistakingly using
      // incorrect function
      throw "This is not a literal type !";
    return this.base;
  }

  Type.prototype.getTypeVar = function(){
    if(!this.isTypeVar())
      throw "This is not a type variable !";
    return this.base.substring(6);
  }
  
  // Is arrow type a -> b ?
  Type.prototype.isFunction = function(){
    return this.next != null;
  }
  // If function, get the first part a -> b 
  Type.prototype.getFirst = function(){
    if(!this.isFunction())
      throw "This is not a function !";
    return this.base;
  }

  // If function, get the second part a -> b
  Type.prototype.getSecond = function(){
    if(!this.isFunction())
      throw "This is not a function !";
    return this.next;
  }

  Type.prototype.toString = function(){
    var str = "";
    if(this.isTypeVar())
      str = this.getTypeVar();
    else if (this.isLiteral())
      str = this.getLiteral();
    else
      str = this.getFirst().toString() + " -> " + this.getSecond().toString();
    return str;
  }

  Type.flatten = function(tp){
    var tps = [];
    while(tp.next){
      tps.push(new Type(tp.base));
      tp = tp.next;
    }
    tps.push(new Type(tp.base));
    return tps;
  }

  Type.fromList = function(ls){
    if(ls.length == 1)
      return new Type(ls[0]);

    return new Type(new Type(ls[0]), Type.fromList(ls.splice(1)));
  }

  // Get free type variables
  // ftv :: Type -> Set String
  Type.ftv = function(tp){
    if (tp.isTypeVar())
      return new Set([tp.getTypeVar()]);
    else if (tp.isLiteral())
      return new Set([]);
    else 
      return Set.union(Type.ftv(tp.getFirst()), Type.ftv(tp.getSecond()));
  }


  // Apply substitutions
  // apply : Dictionary String Type -> Type -> Type
  Type.apply = function(s, t){
    try{t.isTypeVar()}catch(e){console.log(e.stack)};
    if (t.isTypeVar()){
      var n = t.getTypeVar();
      if(s[n] == null)
        return t;
      else
        return s[n];
    }
    else if (t.isFunction()){
      return new Type(Type.apply(s,t.getFirst()), Type.apply(s, t.getSecond()));
    }
    else
      return t;
  }

  Type.composeSubst = function(s1,s2){
    var s2n = {};
    for (var key in s2) {
      if (s2.hasOwnProperty(key)) {
        var n = Type.apply(s1, s2[key]);
        s2n[key] = n;
      }
    }
    // Union is left-biased
    for(var key in s1){
      if (s1.hasOwnProperty(key)) {
        if(!s2n[key])
          s2n[key] = s1[key];
      }
    }
    return s2n;
  }

  // Most general unifier
  // mgu : Type -> Type -> Dictionary String Type
  Type.mgu = function(t1, t2){
    if (t1.isFunction() && t2.isFunction()){
      var s1 = Type.mgu(t1.getFirst(), t2.getFirst());

      var arg1 = Type.apply(s1, t1.getSecond());
      var arg2 = Type.apply(s1, t2.getSecond());
      var s2 = Type.mgu(arg1,arg2);
      return Type.composeSubst(s1,s2); 
    }
    else if(t1.isTypeVar()){
      var u = t1.getTypeVar();
      return Type.varBind(u,t2);
    }
    else if(t2.isTypeVar()){
      var u = t2.getTypeVar();
      return Type.varBind(u,t1);
    }
    else if(t1.isLiteral() && t2.isLiteral() && t1.getLiteral() ===
        t2.getLiteral()){
      return {};
    }
    else{
      throw "types do not unify: " + t1.toString() + " and " + t2.toString();
    }
  }

  // u - String, t - Type
  Type.varBind = function(u,t){
    if (t.isTypeVar() && t.getTypeVar() == u)
      return {};
    else if ( Type.ftv(t).has(u) )
      throw "occur check fails " + u + " vs " + t.toString();
    else{
      var singleton = {};
      singleton[u] = t;
      return singleton;
    }
  };

    // Global state
  var tiSupply = 0;
  var tiSubst = {};
  var tiEnv = {};

  Type.generateTypeVar = function(prefix){
    var tv = new Type("_POLY_" + prefix + tiSupply);
    tiSupply++;
    return tv;
  }

  Scheme = function(varNames, tp){
    this.varNames = varNames;
    this.tp = tp;
  }
  Scheme.ftv = function(scheme){
    var s = Type.ftv(scheme.tp);
    this.varNames.forEach(function(varName){
      s.delete(varName);
    });
    return s;
  }
  Scheme.apply = function(s, scheme){
    // Hope this is ok. s should actually be immutable and we should be working
    // on a different copy of the variable
    this.varNames.forEach(function(varName){
      delete s[varName];
    });
    return new Scheme(scheme.varNames, Type.apply(s, scheme.type));
  }
  Scheme.instantiate = function(scheme){
    var nvars = [];
    var s = {}; // s : Map String Type
    scheme.varNames.forEach(function(varName){
      var n = Type.generateTypeVar("a");
      s[varName] = n;
    });
    return Type.apply(s, this.type); // return : Type
  }

  
  EVar = function(varName){this.varName = varName};
  ELit = function(lit){this.lit = lit};
  EApp = function(exp1, exp2){this.exp1 = exp1; this.exp2 = exp2};
  EAbs = function(varName, exp){this.varName = varName; this.exp = exp};
  ELet = function(varName, exp1, exp2){this.varName = varName; this.exp1 = exp1;
    this.exp2 = exp2};

  Exp = function(exp){
    this.exp = exp;
  }
  Exp.prototype.isVar = function(){return this.exp instanceof EVar;};
  Exp.prototype.getVarName = function(){
    if(!this.isVar()) throw "Not a var expression !";
    return this.exp.varName;
  }

  Exp.prototype.isLit = function(){return this.exp instanceof ELit;};
  Exp.prototype.getLiteral = function(){
    if(!this.isLit()) throw "Not a literal expression !";
    return this.exp.lit;
  }

  Exp.prototype.isApp = function(){return this.exp instanceof EApp;};
  Exp.prototype.getAppExpFirst = function(){
    if(!this.isLit()) throw "Not a application expression !";
    return this.exp.exp1;
  }
  Exp.prototype.getAppExpSecond = function(){
    if(!this.isLit()) throw "Not a application expression !";
    return this.exp.exp2;
  }

  Exp.prototype.isAbs = function(){return this.exp instanceof EAbs;};
  Exp.prototype.getAbsVarName = function(){
    if(!this.isAbs()) throw "Not a abstraction expression !";
    return this.exp.varName;
  }
  Exp.prototype.getAbsExp = function(){
    if(!this.isAbs()) throw "Not a abstraction expression !";
    return this.exp.exp;
  }

  Exp.prototype.isLet = function(){return this.exp instanceof ELet;};
  Exp.prototype.getLetVarName = function(){
    if(!this.isLet()) throw "Not a Let expression !";
    return this.exp.varName;
  }
  Exp.prototype.getLetExpFirst = function(){
    if(!this.isLet()) throw "Not a Let expression !";
    return this.exp.exp1;
  }
  Exp.prototype.getLetExpSecond = function(){
    if(!this.isLet()) throw "Not a Let expression !";
    return this.exp.exp2;
  }

  // Shallow copy
  copyDic = function(dic){
    var dicn = {};
    for (var key in dic) {
      if (dic.hasOwnProperty(key)) {
        dicn[key] = dic[key];
      }
    }
    return dicn;
  }

  // Algorithm W
  // env : Map String Scheme
  // exp : Exp
  
  // TypeEnv Map String Scheme
  TypeEnv = function(env){
    this.env = env;
  }
  
  TypeEnv.prototype.copy = function(){
    return new TypeEnv(copyDic(this.env));
  }

  TypeEnv.apply = function(s, te){
    var env = te.env;
    var envn = copyDic(env);
    for (var key in env) {
      if (env.hasOwnProperty(key)) {
        envn[key] = Scheme.apply(s, env[key]);
      }
    }
    return envn;
  };
  TypeEnv.ftv = function(te){
    var env = te.env;
    var vals = {}; // vals : [
    for (var key in env) {
      if (env.hasOwnProperty(key)) {
        vals.push(env[key]);
      }
    } 
  };
  TypeEnv.remove = function(te, x){
    var ten = te.copy();
    delete ten.env[x];
    return ten;
  };

  TypeEnv.prototype.insert = function(x,t){
    this.env[x] = t;
  };

  TypeEnv.generalize = function(te,t){
    var a = Type.ftv(t);
    var b = TypeEnv.ftv(te);
    b.forEach(function(it){
      a.remove(it);
    });
    var vs = [];
    a.forEach(function(it){
      vs.push(it);
    });
    return a;
  };

  ftvList = function(ls){
    var s = new Set([]);
    var ftv = eval(ls[0].constructor.name + "." + "ftv");
    ls.map(ftv).forEach(function(l){
      s.add(l);
    });
    return s;
  };
  applyList = function(s,ls){
    var s = new Set([]);
    var lsn = [];
    var apply = eval(ls[0].constructor.name + "." + "apply");
    ls.forEach(function(l){
      lsn.apply(s,l);
    });
    return lsn;
  };




  Exp.ti = function(te, exp){
    var env = te.env;
    if(exp.isVar()){
      var n = exp.getVarName();
      if(env[n]){
        var sigma = env[n]; // sigma : Scheme
        var t = Scheme.instantiate(sigma);
        return [{}, t];
      }
      else{
        throw "Unbound variable" + n;
      }
    }
    else if(exp.isLiteral()){
      return [{}, new Type("Integer")]; // Expand here
    }
    else if(exp.isAbs()){
      var n = exp.getAbsVarName();
      var e = exp.getAbsExp();
      var tv = Type.generateTypeVar();
      var ten = TypeEnv.remove(te, n);
      ten.insert(n,new Scheme([],tv));
      var k = Exp.ti(ten,e);
      var s1 = k[0]; var t1 = k[1];
      return [s1, new Type(Type.apply(s1,tv), t1)];
    }
    else if(exp.isApp()){
      var e1 = exp.getAppExpFirst();
      var e2 = exp.getAppExpSecond();
      var tv = Type.generateTypeVar();
      var k1 = Exp.ti(env, e1); var s1 = k1[0]; var t1= k1[1];
      var k2 = Exp.ti(TypeEnv.apply(s1,env), e2); var s2 = k2[0]; var t2 = k2[1];
      var k3 = Type.mgu(Type.apply(s2,t1), new Type(t2,tv));
      return [Type.composeSubst(s3,Type.composeSubst(s2,s1)), Type.apply(s3,tv)];
    }
    else if (exp.isLet()){
      var x = exp.getLetVarName();
      var e1 = exp.getLetExpFirst();
      var e2 = exp.getLetExpSecond();
      var k1 = ti(env, e1); var s1 = k1[0]; var t1 = k1[1];
      var ten = TypeEnv.remove(te,x);
      var tn = generalize(TypeEnv.apply(s1,ten),t1);
      envn.insert(x,tn); 
      var k2 = Exp.ti(TypeEnv.apply(s1,ten), e2);
      return [Type.composeSubsts(s1,s2),t2];
    }
  }

  var t = new Type("Int");
  var u = new Type("_POLY_A");
  var i = new Type("Int");
  var r = Type.fromList(["Int","Float","_POLY_A"]);
  var y = Type.fromList(["_POLY_A","_POLY_B","_POLY_A"]);
  var f = Type.flatten(r);

  // test mgu
  var z = Type.mgu(r,y);
  console.log(z);

