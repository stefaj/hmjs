  // All js boys

  // Type = TypeVar
  //      | Literal
  //      | Function this next

  // Returns a new set with distinct elements from s1 and s2
  /**
   * @param {Set} s1
   * @param {Set} s2
   * @return {Set}
   */
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
  /**
   * @constructor
   * @param {(Type|string|null)} base
   * @param {Type=} next
   */
  Type = function(base, next){
    this.base = base;
    this.next = next;
  }

  Type.prototype.isTypeVar = function(){
    return !this.isFunction() && this.base.startsWith("_POLY_");
  }

  Type.prototype.isLiteral = function(){
    return !this.isTypeVar() && !this.isFunction();
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

  /**
   * @param {Type} tp
   * @return {Array<Type>}
   */
  Type.flatten = function(tp){
    var tps = [];
    while(tp.next){
      tps.push(new Type(tp.base));
      tp = tp.next;
    }
    tps.push(new Type(tp.base));
    return tps;
  }
  
  /**
   * @param {Array<string>} ls
   * @return {Type}
   */
  Type.fromList = function(ls){
    if(ls.length == 1)
      return new Type(ls[0]);

    return new Type(new Type(ls[0]), Type.fromList(ls.splice(1)));
  }

  // Get free type variables
  // ftv :: Type -> Set String
  /**
   * @param {Type} tp
   * @return {Set}
   */
  Type.ftv = function(tp){
    if (tp.isTypeVar())
      return new Set([tp.getTypeVar()]);
    else if (tp.isLiteral())
      return new Set([]);
    else 
      return Set.union(Type.ftv(tp.getFirst()), Type.ftv(tp.getSecond()));
  }


  // apply : Dictionary String Type -> Type -> Type
  /**
   * Apply substitutions
   * @param {Object} s
   * @param {Type} t a type
   * @return {Type}
   */
  Type.apply = function(s, t){
    try{t.isTypeVar()}catch(e){
      console.log(t);
      console.log(e.stack)};
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

  /**
   * @param {Object<string, Type>} s1
   * @param {Object<string, Type>} s2
   * @return {Object<string, Type>}
   */
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

  /**
   * Most general unifier
   * @param {Type} t1 first type
   * @param {Type} t2 second type
   * @return {Object<string, Type>}
   */
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

  /**
   * @param {string} u name of variable
   * @param {Type} t type of variable
   * @return {Object<string, Type>}
   */
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

  /**
   * @param {string} prefix
   * @return {Type}
   */
  Type.generateTypeVar = function(prefix){
    var tv = new Type("_POLY_" + prefix + tiSupply);
    tiSupply++;
    return tv;
  }

  /**
   * @constructor
   */
  Scheme = function(varNames, tp){
    this.varNames = varNames;
    this.tp = tp;
  };

  /**
   * We only use it for schemes anyway
   * @param {Array<Scheme>} ls
   * @return {Set}
   */
  Scheme.ftvList = function(ls){
    var s = new Set([]);
    if(ls.length == 0) return s;
    ls.map(Scheme.ftv).forEach(function(l){
      s.add(l);
    });
    return s;
  };

  /**
   * @return {Scheme}
   */
  Scheme.prototype.copy = function(){
    var tp = this.tp;
    var varNames = [];
    this.varNames.forEach(function(v){
      varNames.push(v);
    });
    return new Scheme(varNames, tp);
  };

  /**
   * @param {Scheme} scheme
   * @return {Set}
   */
  Scheme.ftv = function(scheme){
    var s = Type.ftv(scheme.tp);
    scheme.varNames.forEach(function(varName){
      s.delete(varName);
    });
    return s;
  };

  /**
   * @param {Object} s
   * @param {Scheme} scheme
   * @return {Scheme}
   */
  Scheme.apply = function(s, scheme){
    // Hope this is ok. s should actually be immutable and we should be working
    // on a different copy of the variable
    if(! (scheme instanceof Scheme) )
      throw "Can only apply on Schemes !";  
    var sn = copyDic(s);
    scheme.varNames.forEach(function(varName){
      delete sn[varName];
    });

    return new Scheme(scheme.varNames, Type.apply(sn, scheme.tp));
  }
  
  /**
   * @param {Scheme} scheme
   * @return {Type}
   */
  Scheme.instantiate = function(scheme){
    if (! (scheme instanceof Scheme))
      throw "Can only instantiate schemes !";
    var nvars = [];
    var s = {}; // s : Map String Type
    scheme.varNames.forEach(function(varName){
      var n = Type.generateTypeVar("a");
      s[varName] = n;
    });
    return Type.apply(s, scheme.tp); // return : Type
  }

  
  /**
   * @constructor
   */
  EVar = function(varName){
    this.varName = varName
  };
  EVar.prototype.toString = function(){
    return this.varName; 
  };
  /**
   * @constructor
   */
  ELit = function(lit){
    this.lit = lit
  };
  ELit.prototype.toString = function(){ return this.lit; };
  /**
   * @constructor
   */
  EApp = function(exp1, exp2){
    this.exp1 = exp1; this.exp2 = exp2
  };
  EApp.prototype.toString = function(){ return "(" + this.exp1.toString() + ")(" + this.exp2.toString() + ")";};
  /**
   * @constructor
   */
  EAbs = function(varName, exp){
    this.varName = varName; this.exp = exp
  };
  EAbs.prototype.toString = function(){ return "\\" + this.varName + " -> " + this.exp.toString();};
  /**
   * @constructor
   */
  ELet = function(varName, exp1, exp2){
    this.varName = varName; 
    this.exp1 = exp1;
    this.exp2 = exp2
  };
  ELet.prototype.toString = function(){ return "let " + this.varName + " = " + this.exp1.toString() + " in " + this.exp2.toString(); };

  /**
   * @constructor
   */
  Exp = function(exp){
    this.exp = exp;
  }
  Exp.prototype.toString = function(){
    return this.exp.toString();
  }
  // Static constructor helpers
  /**
   * @return {Exp}
   */
  Exp.Var = function(varName){
    return new Exp(new EVar(varName));
  }
  /**
   * @return {Exp}
   */
  Exp.Lit = function(lit){
    return new Exp(new ELit(lit));
  }
  /**
   * @return {Exp}
   */
  Exp.App = function(exp1, exp2){
    return new Exp(new EApp(exp1, exp2));
  }
  /**
   * @return {Exp}
   */
  Exp.Abs = function(varName, exp){
    return new Exp(new EAbs(varName, exp));
  }
  /**
   * @return {Exp}
   */
  Exp.Let = function(varName, exp1, exp2){
    return new Exp(new ELet(varName, exp1, exp2));
  }

  Exp.prototype.isVar = function(){return this.exp instanceof EVar;};
  Exp.prototype.getVarName = function(){
    if(!this.isVar()) throw "Not a var expression !";
    return this.exp.varName;
  }

  Exp.prototype.isLiteral = function(){return this.exp instanceof ELit;};
  Exp.prototype.getLiteral = function(){
    if(!this.isLiteral()) throw "Not a literal expression !";
    return this.exp.lit;
  }

  Exp.prototype.isApp = function(){return this.exp instanceof EApp;};
  Exp.prototype.getAppExpFirst = function(){
    if(!this.isApp()) throw "Not an application expression !";
    return this.exp.exp1;
  }
  Exp.prototype.getAppExpSecond = function(){
    if(!this.isApp()) throw "Not an application expression !";
    return this.exp.exp2;
  }

  Exp.prototype.isAbs = function(){return this.exp instanceof EAbs;};
  Exp.prototype.getAbsVarName = function(){
    if(!this.isAbs()) throw "Not an abstraction expression !";
    return this.exp.varName;
  }
  Exp.prototype.getAbsExp = function(){
    if(!this.isAbs()) throw "Not an abstraction expression !";
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
  /**
   * @constructor
   * @param {Object<string, Scheme>} env
   */
  TypeEnv = function(env){
    this.env = {};
    for (var key in env) {
      if (env.hasOwnProperty(key)) {
        /**
         * @type {Scheme}
         */
        var envk = env[key];
        if( ! (envk instanceof Scheme)){
          console.log(envk);
          throw "Must be a Scheme ! ";
        }
        this.env[key] = envk.copy();
      }
    }
  }
  
  // returns TypeEnv
  /**
   * @return {TypeEnv}
   */
  TypeEnv.prototype.copy = function(){
    return new TypeEnv(copyDic(this.env));
  }

  // Dic String Type -> TypeEnv -> TypeEnv
  /**
   * @param {Object} s
   * @param {TypeEnv} te
   * @return {TypeEnv}
   */
  TypeEnv.apply = function(s, te){
    if(! (te instanceof TypeEnv) ){
      console.log(te);
      throw "Not a TypeEnvironment";
    }
    var env = te.env;
    var envn = copyDic(env);
    for (var key in env) {
      if (env.hasOwnProperty(key)) {
        if(! (env[key] instanceof Scheme) )
          throw "Element must be a Scheme";
        
        envn[key] = Scheme.apply(s, env[key]);
        if (! (envn[key] instanceof Scheme))
          throw "For some reason Scheme.apply does not return a Scheme";
      }
    }
    return new TypeEnv(envn);
  };
  
  /**
   * @param {TypeEnv} te
   * @return {Set}
   */
  TypeEnv.ftv = function(te){
    if( ! (te instanceof TypeEnv))
      throw "Must be applied to a TypeEnv";

    var env = te.env;
    var vals = []; // vals : [Scheme]
    for (var key in env) {
      if (env.hasOwnProperty(key)) {
        vals.push(env[key]);
      }
    } 
    return Scheme.ftvList(vals);
  };

  /**
   * @param {TypeEnv} te
   * @param {string} x
   * @return {TypeEnv}
   */
  TypeEnv.remove = function(te, x){
    if ( ! (te instanceof TypeEnv))
      throw "Can only remove from TypeEnv";
    
    try{te.copy()}catch(e){
      console.log(te);
      console.log(e.stack)};

    var ten = te.copy();
    delete ten.env[x];
    return ten;
  };

  /**
   * @param {string} x
   * @param {Scheme} s
   * @param {TypeEnv} te
   * @return {TypeEnv}
   */
  TypeEnv.insert = function(x,s,te){
    if (! (s instanceof Scheme) )
      throw "Can only insert Schemes !";
    var ten = te.copy();
    ten.env[x] = s;
    return ten;
  };

  // generalize : TypeEnv -> Type -> Scheme
  /**
   * @param {TypeEnv} te
   * @param {Type} t
   * @return {Scheme}
   */
  TypeEnv.generalize = function(te,t){
    if( ! (te instanceof TypeEnv))
      throw "Must be applied to TypeEnv";
    if ( ! (t instanceof Type))
      throw "Must be applied to Type";
    var a = Type.ftv(t);
    var b = TypeEnv.ftv(te);
    b.forEach(function(it){
      a.delete(it);
    });
    var vars = [];
    a.forEach(function(it){
      vars.push(it);
    });
    return new Scheme(vars,t);
  };

    /*applyList = function(s,ls){
    var lsn = [];
    var apply = eval(ls[0].constructor.name + "." + "apply");
    ls.forEach(function(l){
      lsn.push(apply(s,l));
    });
    return lsn;
  };*/



  /**
   * @param {TypeEnv} te
   * @param {Exp} exp
   * @return {{sub : Object<string, Type>, tp : Type}}
   */
  Exp.ti = function(te, exp){
    if(! (te instanceof TypeEnv)){
      throw "Must supply a TypeEnv";
    }
    var env = te.env;

    if(exp.isVar()){
      var n = exp.getVarName();
      if(env[n]){
        /**
         * @type {Scheme}
         */
        var sigma = env[n]; // sigma : Scheme
        if ( ! (sigma instanceof Scheme))
          throw "sigma must be a Scheme !"
        var t = Scheme.instantiate(sigma);
        return {sub:{}, tp:t};
      }
      else{
        throw "Unbound variable " + n;
      }
    }
    else if(exp.isLiteral()){
      return {sub:{}, tp : new Type("Integer")}; // Expand here
    }
    else if(exp.isAbs()){
      var n = exp.getAbsVarName();
      var e = exp.getAbsExp();
      var tv = Type.generateTypeVar('a');
      var ten = TypeEnv.remove(te, n);
      var tenn = TypeEnv.insert(n,new Scheme([],tv),ten);
      var k = Exp.ti(tenn,e);
      var s1 = k['sub']; var t1 = k['tp'];
      //console.log(Type.apply(s1,tv));
      //console.log(t1);
      //console.log(new Type(Type.apply(s1,tv), t1) );
      var res = new Type(Type.apply(s1,tv), t1);
      if( ! (res instanceof Type))
        throw "Must be type damnit";
      return {sub : s1, tp : res};
    }
    else if(exp.isApp()){
      var e1 = exp.getAppExpFirst();
      var e2 = exp.getAppExpSecond();
      var tv = Type.generateTypeVar('a');

      var k1 = Exp.ti(te, e1); var s1 = k1['sub']; var t1= k1['tp'];
      var k2 = Exp.ti(TypeEnv.apply(s1,te), e2); var s2 = k2['sub']; var t2 = k2['tp'];
      var s3 = Type.mgu(Type.apply(s2,t1), new Type(t2,tv));

      return {sub : Type.composeSubst(s3,Type.composeSubst(s2,s1)), tp : Type.apply(s3,tv)};
    }
    else if (exp.isLet()){
      var x = exp.getLetVarName();
      var e1 = exp.getLetExpFirst();
      var e2 = exp.getLetExpSecond();
      var k1 = Exp.ti(te, e1); var s1 = k1['sub']; var t1 = k1['tp'];
      var ten = TypeEnv.remove(te,x);
      var tn = TypeEnv.generalize(TypeEnv.apply(s1,ten),t1);
      var tenn = TypeEnv.insert(x,tn,ten); 
      var k2 = Exp.ti(TypeEnv.apply(s1,tenn), e2); var s2 = k2['sub']; var t2 = k2['tp'];
      return { sub : Type.composeSubst(s1,s2), tp : t2 };
    }
    throw "Partial pattern match";
  }

  /**
   * @param {Object<string,Scheme>} env
   * @param {Exp} e
   */
  Exp.typeInference = function(env, e){
    // Reset state
    tiSupply = 0;

    var k = Exp.ti(new TypeEnv(env), e);

    var s = k['sub']; var t = k['tp'];
    return Type.apply(s,t);
  }

  var t = new Type("Int");
  var u = new Type("_POLY_A");
  var i = new Type("Int");
  // var f = Type.flatten(r);

  // test mgu
  var r = Type.fromList(["Int","Float","_POLY_A"]);
  var y = Type.fromList(["_POLY_A","_POLY_B","_POLY_A"]);
  var z = Type.mgu(r,y);
  var o = Type.fromList(["Int","_POLY_A","_POLY_A"]);
  var p = Type.fromList(["_POLY_B","_POLY_A","_POLY_A"]);
  var x = Type.mgu(o,p);
  //console.log(z);
  //console.log(x);

  // test ti
  var e0 = Exp.Abs('x', Exp.Var('x'));
  var e1 = Exp.App(e0, Exp.Lit('10'));
  var e2 = Exp.Let("id", e0, Exp.App(Exp.Var("id"), Exp.Lit('20')));
  var e3 = Exp.Let("id", e0, Exp.Var("id"));

  var t0 = Exp.typeInference({},e0);
  console.log(e0.toString());
  console.log(t0.toString());

  var t1 = Exp.typeInference({},e1);
  console.log(e1.toString());
  console.log(t1.toString());

  var t2 = Exp.typeInference({},e2);
  console.log(e2.toString());
  console.log(t2.toString());

  var t3 = Exp.typeInference({},e3);
  console.log(e3.toString());
  console.log(t3.toString());


  var e4 = Exp.App( Exp.Var('+'), Exp.Lit('10'));
  var pt = Type.fromList(["Integer","Integer","Integer"]);
  var s = new Scheme(['+'],pt) 
  var t4 = Exp.typeInference({'+' :s },e4);
  //console.log(s);
  //console.log(e4.toString());
  //console.log(t4.toString());

  var e5 = Exp.App(e4, Exp.Lit('20'));
  var t5 = Exp.typeInference({'+':s},e5);
  console.log(e5.toString());
  //console.log(t5.toString());

