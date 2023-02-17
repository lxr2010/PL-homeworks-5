module Stlc = {
  type rec typ = TInt | TBool | TVar(string) | TArr(typ, typ)
  type rec expr = CstI(int) | CstB(bool) | Var(string)
    | If(expr, expr, expr)
    | Fun(string, expr) | App(expr, expr)
    | Add(expr, expr)

  let rec toString = (t: typ) => switch t {
    | TInt => "Int"
    | TBool => "Bool"
    | TVar(x) => "T_"++x
    | TArr(x,y) => "( " ++ toString(x) ++ " -> " ++ toString(y) ++ " )"
  }


  let tvar_cnt = ref(0)
  let new_tvar = () : typ => {
    tvar_cnt.contents = tvar_cnt.contents + 1
    TVar("@*"++Js.Int.toString(tvar_cnt.contents))
  }

  type constraints = list<(typ,typ)>
  type context = list<(string, typ)>
  type subst = list<(string, typ)>

  let toStringCstr = (cs: constraints) => {
    let mapDictToString = (d:(typ,typ)) => {
      let (t1:typ, t2:typ) = d
      "("++ t1->toString ++ ","  ++ t2->toString ++")"
    }
    switch cs {
      | list{} => ""
      | list{h, ...rest} => List.fold_left((a,b)=>a++";"++b->mapDictToString, h->mapDictToString, rest)
    }
  }

  let toStringSubst = (s: subst) => {
    let mapDictToString = (d:(string, typ)) => {
      let (x, t) = d 
      TVar(x)->toString ++ " |-> " ++ t->toString 
    }
    switch s {
      | list{} => ""
      | list{h, ...rest} => List.fold_left((a,b)=>a++","++b->mapDictToString, h->mapDictToString, rest)
    }
  }

  let rec check_expr = (ctx: context, expr: expr) : (typ, constraints) => 
    switch expr {
      | CstI(_) => (TInt, list{})
      | CstB(_) => (TBool, list{})
      | Var(s) =>  switch ctx->Belt.List.getAssoc(s,(a,b)=>a==b) {
        | Some (ts) => (ts, list{})
        | _ => assert false // As for well-formed expr, no Var is used before declaration
      }
      | If(cond, bTrue, bFalse) => {
        let tx = new_tvar()
        let (t1, c1) = check_expr(ctx, cond)
        let (t2, c2) = check_expr(ctx, bTrue)
        let (t3, c3) = check_expr(ctx, bFalse)
        (tx, Belt.List.concatMany([c1, c2, c3, list{(t1,TBool),(t2,tx),(t3,tx)}]))
      }
      | Fun(x, e) => {
        let tx = new_tvar()
        let (te, c) = check_expr(list{(x, tx), ...ctx}, e)
        (TArr(tx, te), c)
      }
      | App(e1, e2) => {
        let tx = new_tvar()
        let (t1, c1) = check_expr(ctx, e1)
        let (t2, c2) = check_expr(ctx, e2)
        (tx, Belt.List.concatMany([c1, c2, list{(t1, TArr(t2, tx))}]))
      }
      | Add(e1, e2) => {
        let tx = new_tvar()
        let (t1, c1) = check_expr(ctx, e1)
        let (t2, c2) = check_expr(ctx, e2)
        (tx, Belt.List.concatMany([c1, c2, list{(tx,TInt),(t1,TInt),(t2,TInt)}]))
      }
    }

  // tell if TVar(x) is in type expression t
  let rec occurs = (x: string,t: typ) : bool => switch t {
    | TInt | TBool => false 
    | TVar(s) if s == x => true 
    | TVar(_) => false 
    | TArr(t1, t2) => occurs(x, t1) || occurs(x, t2)
  }

  // replace all TVar(x) in type expression s with type t
  let rec tvar_subst = (x: string, s: typ, t: typ) : typ => switch s {
    | TInt | TBool => s 
    | TVar(a) if a == x => t 
    | TVar(_) => s 
    | TArr(t1, t2) => TArr(tvar_subst(x, t1, t), tvar_subst(x, t2, t)) 
  }

  let tvar_list_subst = (x: string, r:constraints, t:typ): constraints => {
    let mapDict = (d) => {
      let (t1, t2) = d 
      (tvar_subst(x, t1, t), tvar_subst(x, t2, t))
    } 
    let sameKeyVal = (d) => {
      let (t1, t2) = d 
      (t1 == t2)
    }
     
    // remove identical type bindings
    r->Belt.List.map(mapDict)->Belt.List.keep((a) => !sameKeyVal(a))
  }

  let solve = (cs: constraints) : subst => {
    let rec go = (cs:constraints, s:subst): subst => {
      switch cs {
        | list{} => s 
        | list{c, ...rest} => switch c {
          |(TInt, TInt) | (TBool, TBool) => go(rest, s)
          |(TArr(t1, t2), TArr(t3, t4)) => go(list{(t1,t3),(t2,t4), ...rest}, s)
          |(TVar(x), t) | (t, TVar(x)) => {
            if (occurs(x, t)) {
              Js.log("Can't resolve these constraints.")
              assert false
            }
            go( tvar_list_subst(x, rest, t) , list{(x,t), ...s})
          }
          | _ => {
            Js.log("Wrong type constraint:" ++ toStringCstr(list{c}))
            assert false
          }
        }
      }
    }
    go(cs,list{})
  }

  let type_subst = (t: typ, s: subst) : typ => {
    let rec real_type = (t:typ, s: subst):typ => switch t {
      | TInt | TBool => t 
      | TVar(x) => switch s->Belt.List.getAssoc(x,(a,b)=>a==b) {
        | Some(tx) => real_type(tx, s) 
        | _ => t // might exist variable with no specific type
      }
      | TArr(t1, t2) => TArr(real_type(t1,s), real_type(t2,s))
    }

    let s_reduced = {
      let mapDict = (d) => {
        let (k, st) = d 
        (k, real_type(st, s))
      }
      s->Belt.List.map(mapDict)
    } 
    let get_cached_real_type = (x: string): typ => switch s_reduced->Belt.List.getAssoc(x, (a,b)=>a==b) {
        | Some (tx) => tx 
        | _ => TVar(x)
    }
    let rec go = (t: typ): typ => switch t {
      | TInt | TBool => t 
      | TVar(x) => get_cached_real_type(x)
      | TArr(t1, t2) => TArr(go(t1),go(t2))
    }
    go(t)
  }

  let infer = (expr: expr) : typ => { 
    let (t, cs) = check_expr(list{}, expr)
    let s = solve(cs)
    let res = type_subst(t, s)
    res
  }

  let test = Fun("f",
                Fun("a", 
                  Fun("b",If(Var("a"), 
                      Add(App(Var("f"),Var("b")),CstI(1)),
                      App(Var("f"),Var("a"))))))

  let inferred = infer(test)
  Js.log(inferred->toString)

}

module StlcUF = {
  type rec typ = TInt | TBool | TVar(ref<tvar>) | TArr(typ, typ)
    and tvar = Nolink(string) | Linkto(typ)
  type rec expr = CstI(int) | CstB(bool) | Var(string)
    | If(expr, expr, expr)
    | Fun(string, expr) | App(expr, expr)
    | Add(expr, expr)

  let rec toString = (t: typ) => switch t {
    | TInt => "Int"
    | TBool => "Bool"
    | TVar(x) => switch x.contents {
      | Nolink(sx) => "T_"++sx 
      | Linkto(tx) => toString(tx)
    }
    | TArr(x,y) => "( " ++ toString(x) ++ " -> " ++ toString(y) ++ " )"
  }


  let tvar_cnt = ref(0)
  let fresh_name = (): ref<tvar> => {
    tvar_cnt.contents = tvar_cnt.contents + 1
    ref(Nolink("@*"++Js.Int.toString(tvar_cnt.contents)))
  }
  let new_tvar = () : typ => TVar(fresh_name())

    // tell if TVar(x) is in type expression t
  let rec occurs = (x: ref<tvar>,t: typ) : bool => switch t {
    | TInt | TBool => false 
    | TVar(a) if a.contents == x.contents => true 
    | TVar(b) => switch b.contents {
      | Linkto(t') => occurs(x, t')
      | _ => false 
    }
    | TArr(t1, t2) => occurs(x, t1) || occurs(x, t2)
  }

  let rec repr_type = (t:typ): typ => {
    switch t {
      | TVar(tvar: ref<tvar>) => switch tvar.contents {
        | Nolink(_) => t 
        | Linkto(t1) => {
          let t1' = repr_type(t1)
          tvar := Linkto(t1')
          t1'
        }
      }
      | _ => t
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
          if occurs(tvar,t) {
            Js.log("Can't solve these constraints")
            assert false 
          }
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

  let rec check_expr = (ctx: context, expr: expr) : typ => 
    switch expr {
      | CstI(_) => TInt
      | CstB(_) => TBool
      | Var(s) =>  switch ctx->Belt.List.getAssoc(s,(a,b)=>a==b) {
        | Some (ts) => ts
        | _ => assert false // As for well-formed expr, no Var is used before declaration
      }
      | If(cond, bTrue, bFalse) => {
        let tx = new_tvar()
        let t1 = check_expr(ctx, cond)
        let t2 = check_expr(ctx, bTrue)
        let t3 = check_expr(ctx, bFalse)
        unify(t1, TBool)
        unify(t2,tx)
        unify(t3,tx)
        tx
      }
      | Fun(x, e) => {
        let tx = new_tvar()
        let te = check_expr(list{(x, tx), ...ctx}, e)
        TArr(tx, te)
      }
      | App(e1, e2) => {
        let tx = new_tvar()
        let t1 = check_expr(ctx, e1)
        let t2 = check_expr(ctx, e2)
        unify(t1, TArr(t2,tx))
        tx
      }
      | Add(e1, e2) => {
        let tx = new_tvar()
        let t1 = check_expr(ctx, e1)
        let t2 = check_expr(ctx, e2)
        unify(tx,TInt)
        unify(t1,TInt)
        unify(t2,TInt)
        tx
      }
    }

  let infer = (expr: expr) : typ => { 
    let t = check_expr(list{}, expr)
    t
  }

  let test = Fun("f",
                Fun("a", 
                  Fun("b",If(Var("a"), 
                      App(Var("f"),Var("b")),
                      App(Var("f"),Var("a"))))))

  let inferred = infer(test)
  Js.log(inferred->toString)
}