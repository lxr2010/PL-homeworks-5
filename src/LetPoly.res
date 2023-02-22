module LetPoly = {
  type rec typ = TInt | TBool| TVar(ref<tvar>) | TArr(typ, typ) | QVar(string)
  and tvar = Nolink(string) | Linkto(typ)

  type rec expr = CstI(int) | CstB(bool) | Var(string)
    | If(expr, expr, expr)
    | Add(expr, expr)
    | Fun(string, expr) | App(expr, expr)
    | Let(string, expr, expr)


  let rec toString = (t: typ) => switch t {
    | TInt => "Int"
    | TBool => "Bool"
    | TVar(x) => switch x.contents {
      | Nolink(sx) => "T_"++sx 
      | Linkto(tx) => toString(tx)
    }
    | TArr(x,y) => "( " ++ toString(x) ++ " -> " ++ toString(y) ++ " )"
    | QVar(s) => "QT_"++s
  }


  let tvar_cnt = ref(0)
  let fresh_name = (): ref<tvar> => {
    tvar_cnt.contents = tvar_cnt.contents + 1
    ref(Nolink("@*"++Js.Int.toString(tvar_cnt.contents)))
  }
  let new_tvar = () : typ => TVar(fresh_name())

  let inst_map = ref(list{})
  let fresh_inst = (qs: string) : ref<tvar> => {
    let inst_cnt = switch inst_map.contents->Belt.List.getAssoc(qs, (a,b)=>a==b) {
     |Some (n) => n
     |None => 0
    }
    inst_map.contents = Belt.List.setAssoc(inst_map.contents, qs, inst_cnt+1, (a,b)=>a==b)
    ref(Nolink(qs ++ "_" ++ Js.Int.toString(inst_cnt+1)))
  }
  let new_inst = (qs: string) :typ => TVar(fresh_inst(qs))
  

  let inst = (tp: typ):typ  => {
    let rec get_qvars = (t: typ) : list<string> => {
      switch t {
      | TInt | TBool => list{}
      | TVar(x) => switch x.contents  {
        | Nolink(_) => list{}
        | Linkto(rv) => get_qvars(rv)
      }
      | TArr(x, y) => Belt.List.concatMany([get_qvars(x), get_qvars(y)])
      | QVar(qs) => list{qs}
      }
    }
    let qvars = tp->get_qvars->Belt.List.toArray->Belt.Set.String.fromArray->Belt.Set.String.toList
    let subst_map = qvars->Belt.List.map(qs=>(qs,new_inst(qs)))
    let rec subst_inst = (t: typ, m:list<(string,typ)>) : typ => switch t {
      | TInt | TBool => t 
      | TVar(x) => switch x.contents {
        | Nolink(_) => t 
        | Linkto(rv) => subst_inst(rv, m)
      }
      | TArr(x, y)=> TArr(subst_inst(x,m), subst_inst(y,m))
      | QVar(qs) => switch m->Belt.List.getAssoc(qs, (a,b)=>a==b) {
        | Some(r) => r 
        | _ => assert false 
      }
    }
    subst_inst(tp, subst_map)
  }

  
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

  //context will change when finished a let expression, 
  // definitions inside the let expression will be removed from context.
  // Therefore those type variables whose definition cann't be found
  // in context are free type variables

  let map_definition = (p : (string, typ)) => switch p {
      | (_ , TVar(x)) => switch x.contents {
        | Nolink(xs) => Some(xs)
        | _ => None 
      }
      | _ => None
  }

  let free_tvars_in_ctx = (ctx : context): list<string> => {
    let rec get_tvar_nolink_in_typ = (t: typ) : list<string> => switch t {
      | TBool | TInt => list{} 
      | TVar(x) => switch x.contents {
        | Nolink(xs) => list{xs}
        | Linkto(xt) => get_tvar_nolink_in_typ(xt)
      }
      | TArr(x, y) => Belt.List.concatMany([get_tvar_nolink_in_typ(x), get_tvar_nolink_in_typ(y)])
      | QVar(_) => assert false // Rank-1 polymorphism restriction
    } 

    let getKey = (p: (string,typ)) => {
      let (_ , k) = p
      k
    }

    // deduplicate list using Belt.Set.String, prepare to make diff between tvar_definitions
    let tvar_nolink = ctx->Belt.List.map(p=>p->getKey->get_tvar_nolink_in_typ->Belt.List.toArray)->
                Belt.List.toArray->Belt.Array.concatMany->
                Belt.Set.String.fromArray

    let tvar_definitions = ctx->Belt.List.keepMap(map_definition)->Belt.List.toArray->Belt.Set.String.fromArray
    let undefined_tvar = tvar_nolink->Belt.Set.String.diff(tvar_definitions)->Belt.Set.String.toList
    undefined_tvar
  }

  let gen = (ty: typ, ctx: context) : typ => {
    let freetvars = free_tvars_in_ctx(ctx)
    let rec go = (ty:typ , subst:subst): (typ,subst) => switch ty {
      | TInt | TBool => (ty,subst)
      | TVar(x) => switch x.contents {
        | Nolink(xs) => switch subst->Belt.List.getAssoc(xs,(a,b)=>a==b) {
          | Some(qt) => (qt,subst)
          | None => {
            // xs is not a free type var in context.
            // find xs in context to check whether it is constrained.
            switch ctx->Belt.List.keepMap(map_definition)->Belt.List.has(xs,(a,b)=>a==b) {
              | true => (ty,subst) // constrained by context. don't change
              | false => {
                // unconstrained type variable. Generalize it and add to subst list.
                (QVar(xs),list{(xs,QVar(xs)),...subst})
              }
            }
          }
        }
        | Linkto(xt) => {
          let (xt', subst') = go(xt, subst)
          (TVar(ref(Linkto(xt'))),subst')
        }
      }
      | TArr(x, y) => {
        let (x', subst') = go(x, subst)
        let (y', subst'') = go(y, subst')
        (TArr(x',y'),subst'')
      }
      | QVar(_) => assert false // Rank-1 polymorphism restriction
    }
    let (fst,_) = go(ty, freetvars->Belt.List.map(x=>(x,QVar(x))))
    Js.log("Gen: "++ty->toString ++ " ctx: " ++ ctx->toStringSubst)
    fst
  }


  let rec check_expr = (ctx: context, expr: expr) : typ => 
    switch expr {
      | CstI(_) => TInt
      | CstB(_) => TBool
      | Var(s) =>  switch ctx->Belt.List.getAssoc(s,(a,b)=>a==b) {
        | Some (ts) => inst(ts)
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
      | Let(x, e1, e2) => {
        let t1 = check_expr(ctx, e1)
        let ctx' = list{(x, gen(t1, ctx)), ...ctx}
        let t2 = check_expr(ctx', e2)
        Js.log(t2->toString)
        Js.log(ctx'->toStringSubst)
        t2
      }
    }

  let infer = (expr: expr) : typ => { 
    let t = check_expr(list{}, expr)
    t
  }

  let test = Let("h",Fun("f",Let("g",Var("f"),Var("g"))),If(App(Var("h"),CstB(true)),App(Var("h"),CstI(1)),App(Var("h"),CstI(0))))
  let inferred = infer(test)
  Js.log(inferred->toString)

  
}