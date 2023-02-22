module LvLetPoly = {
  type rec typ = TInt | TBool | TArr(typ, typ) | TVar(ref<tvar>) | QVar(string)
    and tvar = Nolink(string,int) | Linkto(typ)

  type rec expr = CstI(int) | CstB(bool) | Var(string)
    | If(expr, expr, expr)
    | Add(expr, expr)
    | Mul(expr, expr)
    | Leq(expr, expr)
    | Fun(string, expr) | App(expr, expr)
    | Let(string, expr, expr)

  let rec toStringE= (e: expr) => switch e {
    | CstI(i) => Js.Int.toString(i)
    | CstB(b) => if b {"True"} else {"False"}
    | Var(s) => s 
    | If(c, e1, e2) => "If (" ++ c->toStringE ++ ") then { " ++ e1->toStringE ++ " } else { " ++ e2->toStringE ++ " }"
    | Add(e1, e2) => "( " ++ e1->toStringE ++ "+" ++ e2->toStringE ++ " )"
    | Mul(e1, e2) => "( " ++ e1->toStringE ++ "*" ++ e2->toStringE ++ " )"
    | Leq(e1, e2) =>  e1->toStringE ++ "<=" ++ e2->toStringE 
    | Fun(x, e) => "fun " ++ x ++ " -> " ++ e->toStringE
    | App(e1, e2) => "( " ++ e1->toStringE ++ " )( " ++ e2->toStringE ++ " )"
    | Let(x, e1, e2) => "let " ++ x ++ " = " ++ e1->toStringE ++ " in " ++ e2->toStringE
  }

  let rec toString = (t: typ) => switch t {
      | TInt => "Int"
      | TBool => "Bool"
      | TVar(x) => switch x.contents {
        | Nolink(sx,lv) => "T" ++Js.Int.toString(lv) ++ "_"++sx 
        | Linkto(tx) => toString(tx)
      }
      | TArr(x,y) => "( " ++ toString(x) ++ " -> " ++ toString(y) ++ " )"
      | QVar(s) => "QT_"++s
    }

  let tvar_cnt = ref(0)
  let fresh_name = (): string => {
    tvar_cnt.contents = tvar_cnt.contents + 1
    "@*"++Js.Int.toString(tvar_cnt.contents)
  }
  let new_tvar = (level:int) : typ => TVar(ref(Nolink(fresh_name(),level)))

  let inst_map = ref(list{})
  let fresh_inst = (qs: string) : string => {
    let inst_cnt = switch inst_map.contents->Belt.List.getAssoc(qs, (a,b)=>a==b) {
     |Some (n) => n
     |None => 0
    }
    let _ = Belt.List.setAssoc(inst_map.contents, qs, inst_cnt+1, (a,b)=>a==b)
    qs ++ "_" ++ Js.Int.toString(inst_cnt+1)
  }
  let new_inst = (qs: string, level:int) :typ => TVar(ref(Nolink(fresh_inst(qs),level)))

  // tell if TVar(x) is in type expression t
  let rec occurs = (x: ref<tvar>,t: typ) : bool => switch t {
    | TInt | TBool => false 
    | TVar(a) if a.contents == x.contents => true 
    | TVar(b) => switch b.contents {
      | Linkto(t') => occurs(x, t')
      | _ => false 
    }
    | TArr(t1, t2) => occurs(x, t1) || occurs(x, t2)
    | QVar(_) => false 
  }

  let rec repr_type = (t:typ): typ => {
    switch t {
      | TVar(tvar: ref<tvar>) => switch tvar.contents {
        | Nolink(_,_) => t 
        | Linkto(t1) => {
          let t1' = repr_type(t1)
          tvar := Linkto(t1')
          t1'
        }
      }
      | _ => t
    }
  }

  let get_level = (tvar: ref<tvar>) : option<int> => switch tvar.contents {
    | Nolink(_, lv) => Some(lv) 
    | _ => assert false 
  }

  // make sure all tvars' level equal or greater than level
  let prune_level = (level: option<int>, ty: typ):() => {
    let rec checker = (t: typ, lv: int) => switch t {
      | TInt | TBool => ()
      | TVar(x) => switch x.contents {
        | Nolink(xs, l) if (l > lv) => {
          x.contents = Nolink(xs, lv)
        }
        | Linkto(xt) => checker(xt, lv)
        | _ => ()
      }
      | TArr(x, y) => {
        checker(x, lv)
        checker(y, lv)
      }
      | QVar(_) => ()
    }
    switch level {
      | Some(l) => checker(ty, l)
      | _ => ()
    } 
  }

  let rec unify = (t1: typ, t2: typ) : unit => {
    let t1' = repr_type(t1) and t2' = repr_type(t2)
    if t1' === t2' { () }
    else {
      switch (t1', t2') {
        | (TInt, TInt) | (TBool, TBool) => ()
        | (TArr(t1, t2),TArr(t3,t4)) => {
          unify(t1,t3)
          unify(t2,t4)
        }
        | (TVar(tvar), t) | (t, TVar(tvar)) => {
          // tvar must be form Nolink(_,_)
          if occurs(tvar,t) {
            Js.log("Can't solve these constraints")
            assert false 
          }
          prune_level(get_level(tvar),t)
          tvar := Linkto(t)
        }
        | _ => {
          Js.log("Wrong constraint : ("++ t1'->toString ++ "," ++ t2'->toString ++")" )
          assert false
        }
      }
    }
  }

  type context = list<(string, typ)>
  type subst = list<(string, typ)>


  let toStringSubst = (s: subst) => {
    let mapDictToString = (d:(string, typ)) => {
      let (x, t) = d 
      x ++ " |-> " ++ t->toString 
    }
    switch s {
      | list{} => ""
      | list{h, ...rest} => List.fold_left((a,b)=>a++","++b->mapDictToString, h->mapDictToString, rest)
    }
  }

  let inst = (ty: typ, level: int) : typ => {
    let rec get_qvars = (t: typ) : list<string> => {
      switch t {
      | TInt | TBool => list{}
      | TVar(x) => switch x.contents  {
        | Nolink(_,_) => list{}
        | Linkto(rv) => get_qvars(rv)
      }
      | TArr(x, y) => Belt.List.concatMany([get_qvars(x), get_qvars(y)])
      | QVar(qs) => list{qs}
      }
    }
    let qvars = ty->get_qvars->Belt.List.toArray->Belt.Set.String.fromArray->Belt.Set.String.toList
    let subst_map = qvars->Belt.List.map(qs=>(qs,new_inst(qs,level)))
    let rec subst_inst = (t: typ, m:list<(string,typ)>) : typ => switch t {
      | TInt | TBool => t 
      | TVar(x) => switch x.contents {
        | Nolink(_,_) => t 
        | Linkto(rv) => subst_inst(rv, m)
      }
      | TArr(x, y)=> TArr(subst_inst(x,m), subst_inst(y,m))
      | QVar(qs) => switch m->Belt.List.getAssoc(qs, (a,b)=>a==b) {
        | Some(r) => r 
        | _ => assert false 
      }
    }
    subst_inst(ty, subst_map)
  }

  let gen = (ty: typ, level: int) : typ => {
    let rec go = (t: typ) : typ => switch t {
      | TInt | TBool => t
      | TVar(x) => switch x.contents {
        | Nolink (xs, xlv) if xlv > level => {
          QVar(xs)
        }
        | Nolink (_, _) => t
        | Linkto(xt) => {
          let xt' = go(xt)
          TVar(ref(Linkto(xt')))
        }
      }
      | TArr(x,y) => {
        TArr(go(x),go(y))
      }
      | QVar(_) => assert false // Rank-1 polymorphism restriction
    }

    let fst = go(ty)
    fst
  }

  let rec check_expr = (ctx: context, expr: expr, level: int) : typ => {
    let res = switch expr {
      | CstI(_) => TInt
      | CstB(_) => TBool
      | Var(s) =>  switch ctx->Belt.List.getAssoc(s,(a,b)=>a==b) {
        | Some (ts) => inst(ts, level)
        | _ => assert false // As for well-formed expr, no Var is used before declaration
      }
      | If(cond, bTrue, bFalse) => {
        let tx = new_tvar(level)
        let t1 = check_expr(ctx, cond, level)
        let t2 = check_expr(ctx, bTrue, level)
        let t3 = check_expr(ctx, bFalse, level)
        unify(t1, TBool)
        unify(t2,tx)
        unify(t3,tx)
        tx
      }
      | Fun(x, e) => {
        let tx = new_tvar(level)
        let te = check_expr(list{(x, tx), ...ctx}, e, level+1)
        TArr(tx, te)
      }
      | App(e1, e2) => {
        let tx = new_tvar(level)
        let t1 = check_expr(ctx, e1, level)
        let t2 = check_expr(ctx, e2, level)
        unify(t1, TArr(t2,tx))
        tx
      }
      | Add(e1, e2) | Mul(e1, e2) => {
        let tx = new_tvar(level)
        let t1 = check_expr(ctx, e1, level)
        let t2 = check_expr(ctx, e2, level)
        unify(tx,TInt)
        unify(t1,TInt)
        unify(t2,TInt)
        tx
      }
      | Leq(e1,e2) => {
        let tx = new_tvar(level)
        let t1 = check_expr(ctx, e1, level)
        let t2 = check_expr(ctx, e2, level)
        unify(tx, TBool)
        unify(t1, TInt)
        unify(t2, TInt)
        tx
      }
      | Let(x, e1, e2) => {
        let tx = new_tvar(level+1)
        let t1 = check_expr(list{(x,tx),...ctx}, e1, level+1)
        let ctx' = list{(x, gen(t1, level)), ...ctx}
        let t2 = check_expr(ctx', e2, level)
        unify(tx, t1)
        Js.log(ctx'->toStringSubst)
        t2
      }
    }
    res 
  }

  let infer = (expr: expr) : typ => { 
    let t = check_expr(list{}, expr, 0)
    t
  }

}

module Test = {
  open! LvLetPoly
  let test0 = Let("h",Fun("f",Let("g",Var("f"),Var("g"))),If(App(Var("h"),CstB(true)),App(Var("h"),CstI(1)),App(Var("h"),CstI(0))))
  let fact = Let("fac",
      Fun("n",If(Leq(Var("n"),CstI(0)), 
                CstI(1),
                Mul(Var("n"),App(Var("fac"),Add(Var("n"),CstI(-1)))))),
      App(Var("fac"),CstI(5)))
  let more_fact = Let("facc",
      Fun("m",Fun("n",If(Leq(Var("n"),CstI(0)), 
                      Var("m"),
                      App(App(Var("facc"),Var("m")),Add(Var("n"),CstI(-1)))))),
      Var("facc"))
  
  let tests = list{
    test0, fact, more_fact
  }

  let run_test = (ts: list<expr>) :  () => {
    ts->Belt.List.forEach(t=>{
      Js.log("Expr: " ++ t->toStringE)
      let inferred = infer(t)
      Js.log(inferred->toString)
    })
  }

  let run = () => {
    let _ = run_test(tests)
  }
}

Test.run()