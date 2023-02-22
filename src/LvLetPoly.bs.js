// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

var List = require("rescript/lib/js/list.js");
var Caml_obj = require("rescript/lib/js/caml_obj.js");
var Belt_List = require("rescript/lib/js/belt_List.js");
var Belt_SetString = require("rescript/lib/js/belt_SetString.js");

function toStringE(e) {
  switch (e.TAG | 0) {
    case /* CstI */0 :
        return e._0.toString();
    case /* CstB */1 :
        if (e._0) {
          return "True";
        } else {
          return "False";
        }
    case /* Var */2 :
        return e._0;
    case /* If */3 :
        return "If (" + toStringE(e._0) + ") then { " + toStringE(e._1) + " } else { " + toStringE(e._2) + " }";
    case /* Add */4 :
        return "( " + toStringE(e._0) + "+" + toStringE(e._1) + " )";
    case /* Mul */5 :
        return "( " + toStringE(e._0) + "*" + toStringE(e._1) + " )";
    case /* Leq */6 :
        return toStringE(e._0) + "<=" + toStringE(e._1);
    case /* Fun */7 :
        return "fun " + e._0 + " -> " + toStringE(e._1);
    case /* App */8 :
        return "( " + toStringE(e._0) + " )( " + toStringE(e._1) + " )";
    case /* Let */9 :
        return "let " + e._0 + " = " + toStringE(e._1) + " in " + toStringE(e._2);
    
  }
}

function toString(_t) {
  while(true) {
    var t = _t;
    if (typeof t === "number") {
      if (t === /* TInt */0) {
        return "Int";
      } else {
        return "Bool";
      }
    }
    switch (t.TAG | 0) {
      case /* TArr */0 :
          return "( " + toString(t._0) + " -> " + toString(t._1) + " )";
      case /* TVar */1 :
          var tx = t._0.contents;
          if (tx.TAG === /* Nolink */0) {
            return "T" + tx._1.toString() + "_" + tx._0;
          }
          _t = tx._0;
          continue ;
      case /* QVar */2 :
          return "QT_" + t._0;
      
    }
  };
}

var tvar_cnt = {
  contents: 0
};

function fresh_name(param) {
  tvar_cnt.contents = tvar_cnt.contents + 1 | 0;
  return "@*" + tvar_cnt.contents.toString();
}

function new_tvar(level) {
  return {
          TAG: /* TVar */1,
          _0: {
            contents: {
              TAG: /* Nolink */0,
              _0: fresh_name(undefined),
              _1: level
            }
          }
        };
}

var inst_map = {
  contents: /* [] */0
};

function fresh_inst(qs) {
  var n = Belt_List.getAssoc(inst_map.contents, qs, (function (a, b) {
          return a === b;
        }));
  var inst_cnt = n !== undefined ? n : 0;
  Belt_List.setAssoc(inst_map.contents, qs, inst_cnt + 1 | 0, (function (a, b) {
          return a === b;
        }));
  return qs + "_" + (inst_cnt + 1 | 0).toString();
}

function new_inst(qs, level) {
  return {
          TAG: /* TVar */1,
          _0: {
            contents: {
              TAG: /* Nolink */0,
              _0: fresh_inst(qs),
              _1: level
            }
          }
        };
}

function occurs(x, _t) {
  while(true) {
    var t = _t;
    if (typeof t === "number") {
      return false;
    }
    switch (t.TAG | 0) {
      case /* TArr */0 :
          if (occurs(x, t._0)) {
            return true;
          }
          _t = t._1;
          continue ;
      case /* TVar */1 :
          var a = t._0;
          if (Caml_obj.equal(a.contents, x.contents)) {
            return true;
          }
          var t$p = a.contents;
          if (t$p.TAG === /* Nolink */0) {
            return false;
          }
          _t = t$p._0;
          continue ;
      case /* QVar */2 :
          return false;
      
    }
  };
}

function repr_type(t) {
  if (typeof t === "number") {
    return t;
  }
  if (t.TAG !== /* TVar */1) {
    return t;
  }
  var tvar = t._0;
  var t1 = tvar.contents;
  if (t1.TAG === /* Nolink */0) {
    return t;
  }
  var t1$p = repr_type(t1._0);
  tvar.contents = {
    TAG: /* Linkto */1,
    _0: t1$p
  };
  return t1$p;
}

function get_level(tvar) {
  var match = tvar.contents;
  if (match.TAG === /* Nolink */0) {
    return match._1;
  }
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "LvLetPoly.res",
          83,
          11
        ],
        Error: new Error()
      };
}

function prune_level(level, ty) {
  var checker = function (_t, lv) {
    while(true) {
      var t = _t;
      if (typeof t === "number") {
        return ;
      }
      switch (t.TAG | 0) {
        case /* TArr */0 :
            checker(t._0, lv);
            _t = t._1;
            continue ;
        case /* TVar */1 :
            var x = t._0;
            var xt = x.contents;
            if (xt.TAG === /* Nolink */0) {
              if (xt._1 > lv) {
                x.contents = {
                  TAG: /* Nolink */0,
                  _0: xt._0,
                  _1: lv
                };
                return ;
              } else {
                return ;
              }
            }
            _t = xt._0;
            continue ;
        case /* QVar */2 :
            return ;
        
      }
    };
  };
  if (level !== undefined) {
    return checker(ty, level);
  }
  
}

function unify(_t1, _t2) {
  while(true) {
    var t2 = _t2;
    var t1 = _t1;
    var t1$p = repr_type(t1);
    var t2$p = repr_type(t2);
    if (t1$p === t2$p) {
      return ;
    }
    var exit = 0;
    var tvar;
    var t;
    var exit$1 = 0;
    if (typeof t1$p === "number") {
      if (t1$p === /* TInt */0) {
        if (typeof t2$p === "number") {
          if (t2$p === /* TInt */0) {
            return ;
          }
          exit = 1;
        } else if (t2$p.TAG === /* TVar */1) {
          exit$1 = 3;
        } else {
          exit = 1;
        }
      } else if (typeof t2$p === "number") {
        if (t2$p === /* TBool */1) {
          return ;
        }
        exit = 1;
      } else if (t2$p.TAG === /* TVar */1) {
        exit$1 = 3;
      } else {
        exit = 1;
      }
    } else {
      switch (t1$p.TAG | 0) {
        case /* TArr */0 :
            if (typeof t2$p === "number") {
              exit = 1;
            } else {
              switch (t2$p.TAG | 0) {
                case /* TArr */0 :
                    unify(t1$p._0, t2$p._0);
                    _t2 = t2$p._1;
                    _t1 = t1$p._1;
                    continue ;
                case /* TVar */1 :
                    exit$1 = 3;
                    break;
                default:
                  exit = 1;
              }
            }
            break;
        case /* TVar */1 :
            tvar = t1$p._0;
            t = t2$p;
            exit = 2;
            break;
        case /* QVar */2 :
            exit$1 = 3;
            break;
        
      }
    }
    if (exit$1 === 3) {
      if (typeof t2$p === "number" || t2$p.TAG !== /* TVar */1) {
        exit = 1;
      } else {
        tvar = t2$p._0;
        t = t1$p;
        exit = 2;
      }
    }
    switch (exit) {
      case 1 :
          console.log("Wrong constraint : (" + toString(t1$p) + "," + toString(t2$p) + ")");
          throw {
                RE_EXN_ID: "Assert_failure",
                _1: [
                  "LvLetPoly.res",
                  130,
                  10
                ],
                Error: new Error()
              };
      case 2 :
          if (occurs(tvar, t)) {
            console.log("Can't solve these constraints");
            throw {
                  RE_EXN_ID: "Assert_failure",
                  _1: [
                    "LvLetPoly.res",
                    123,
                    12
                  ],
                  Error: new Error()
                };
          }
          prune_level(get_level(tvar), t);
          tvar.contents = {
            TAG: /* Linkto */1,
            _0: t
          };
          return ;
      
    }
  };
}

function toStringSubst(s) {
  var mapDictToString = function (d) {
    return d[0] + " |-> " + toString(d[1]);
  };
  if (s) {
    return List.fold_left((function (a, b) {
                  return a + "," + mapDictToString(b);
                }), mapDictToString(s.hd), s.tl);
  } else {
    return "";
  }
}

function inst(ty, level) {
  var get_qvars = function (_t) {
    while(true) {
      var t = _t;
      if (typeof t === "number") {
        return /* [] */0;
      }
      switch (t.TAG | 0) {
        case /* TArr */0 :
            return Belt_List.concatMany([
                        get_qvars(t._0),
                        get_qvars(t._1)
                      ]);
        case /* TVar */1 :
            var rv = t._0.contents;
            if (rv.TAG === /* Nolink */0) {
              return /* [] */0;
            }
            _t = rv._0;
            continue ;
        case /* QVar */2 :
            return {
                    hd: t._0,
                    tl: /* [] */0
                  };
        
      }
    };
  };
  var qvars = Belt_SetString.toList(Belt_SetString.fromArray(Belt_List.toArray(get_qvars(ty))));
  var subst_map = Belt_List.map(qvars, (function (qs) {
          return [
                  qs,
                  new_inst(qs, level)
                ];
        }));
  var subst_inst = function (_t, m) {
    while(true) {
      var t = _t;
      if (typeof t === "number") {
        return t;
      }
      switch (t.TAG | 0) {
        case /* TArr */0 :
            return {
                    TAG: /* TArr */0,
                    _0: subst_inst(t._0, m),
                    _1: subst_inst(t._1, m)
                  };
        case /* TVar */1 :
            var rv = t._0.contents;
            if (rv.TAG === /* Nolink */0) {
              return t;
            }
            _t = rv._0;
            continue ;
        case /* QVar */2 :
            var r = Belt_List.getAssoc(m, t._0, (function (a, b) {
                    return a === b;
                  }));
            if (r !== undefined) {
              return r;
            }
            throw {
                  RE_EXN_ID: "Assert_failure",
                  _1: [
                    "LvLetPoly.res",
                    174,
                    15
                  ],
                  Error: new Error()
                };
        
      }
    };
  };
  return subst_inst(ty, subst_map);
}

function gen(ty, level) {
  var go = function (t) {
    if (typeof t === "number") {
      return t;
    }
    switch (t.TAG | 0) {
      case /* TArr */0 :
          return {
                  TAG: /* TArr */0,
                  _0: go(t._0),
                  _1: go(t._1)
                };
      case /* TVar */1 :
          var xt = t._0.contents;
          if (xt.TAG === /* Nolink */0) {
            if (xt._1 > level) {
              return {
                      TAG: /* QVar */2,
                      _0: xt._0
                    };
            } else {
              return t;
            }
          }
          var xt$p = go(xt._0);
          return {
                  TAG: /* TVar */1,
                  _0: {
                    contents: {
                      TAG: /* Linkto */1,
                      _0: xt$p
                    }
                  }
                };
      case /* QVar */2 :
          throw {
                RE_EXN_ID: "Assert_failure",
                _1: [
                  "LvLetPoly.res",
                  196,
                  19
                ],
                Error: new Error()
              };
      
    }
  };
  return go(ty);
}

function check_expr(ctx, expr, level) {
  switch (expr.TAG | 0) {
    case /* CstI */0 :
        return /* TInt */0;
    case /* CstB */1 :
        return /* TBool */1;
    case /* Var */2 :
        var ts = Belt_List.getAssoc(ctx, expr._0, (function (a, b) {
                return a === b;
              }));
        if (ts !== undefined) {
          return inst(ts, level);
        }
        throw {
              RE_EXN_ID: "Assert_failure",
              _1: [
                "LvLetPoly.res",
                209,
                15
              ],
              Error: new Error()
            };
    case /* If */3 :
        var tx = new_tvar(level);
        var t1 = check_expr(ctx, expr._0, level);
        var t2 = check_expr(ctx, expr._1, level);
        var t3 = check_expr(ctx, expr._2, level);
        unify(t1, /* TBool */1);
        unify(t2, tx);
        unify(t3, tx);
        return tx;
    case /* Add */4 :
    case /* Mul */5 :
        break;
    case /* Leq */6 :
        var tx$1 = new_tvar(level);
        var t1$1 = check_expr(ctx, expr._0, level);
        var t2$1 = check_expr(ctx, expr._1, level);
        unify(tx$1, /* TBool */1);
        unify(t1$1, /* TInt */0);
        unify(t2$1, /* TInt */0);
        return tx$1;
    case /* Fun */7 :
        var tx$2 = new_tvar(level);
        var te = check_expr({
              hd: [
                expr._0,
                tx$2
              ],
              tl: ctx
            }, expr._1, level + 1 | 0);
        return {
                TAG: /* TArr */0,
                _0: tx$2,
                _1: te
              };
    case /* App */8 :
        var tx$3 = new_tvar(level);
        var t1$2 = check_expr(ctx, expr._0, level);
        var t2$2 = check_expr(ctx, expr._1, level);
        unify(t1$2, {
              TAG: /* TArr */0,
              _0: t2$2,
              _1: tx$3
            });
        return tx$3;
    case /* Let */9 :
        var x = expr._0;
        var tx$4 = new_tvar(level + 1 | 0);
        var t1$3 = check_expr({
              hd: [
                x,
                tx$4
              ],
              tl: ctx
            }, expr._1, level + 1 | 0);
        var ctx$p_0 = [
          x,
          gen(t1$3, level)
        ];
        var ctx$p = {
          hd: ctx$p_0,
          tl: ctx
        };
        var t2$3 = check_expr(ctx$p, expr._2, level);
        unify(tx$4, t1$3);
        console.log(toStringSubst(ctx$p));
        return t2$3;
    
  }
  var tx$5 = new_tvar(level);
  var t1$4 = check_expr(ctx, expr._0, level);
  var t2$4 = check_expr(ctx, expr._1, level);
  unify(tx$5, /* TInt */0);
  unify(t1$4, /* TInt */0);
  unify(t2$4, /* TInt */0);
  return tx$5;
}

function infer(expr) {
  return check_expr(/* [] */0, expr, 0);
}

var LvLetPoly = {
  toStringE: toStringE,
  toString: toString,
  tvar_cnt: tvar_cnt,
  fresh_name: fresh_name,
  new_tvar: new_tvar,
  inst_map: inst_map,
  fresh_inst: fresh_inst,
  new_inst: new_inst,
  occurs: occurs,
  repr_type: repr_type,
  get_level: get_level,
  prune_level: prune_level,
  unify: unify,
  toStringSubst: toStringSubst,
  inst: inst,
  gen: gen,
  check_expr: check_expr,
  infer: infer
};

var test0 = {
  TAG: /* Let */9,
  _0: "h",
  _1: {
    TAG: /* Fun */7,
    _0: "f",
    _1: {
      TAG: /* Let */9,
      _0: "g",
      _1: {
        TAG: /* Var */2,
        _0: "f"
      },
      _2: {
        TAG: /* Var */2,
        _0: "g"
      }
    }
  },
  _2: {
    TAG: /* If */3,
    _0: {
      TAG: /* App */8,
      _0: {
        TAG: /* Var */2,
        _0: "h"
      },
      _1: {
        TAG: /* CstB */1,
        _0: true
      }
    },
    _1: {
      TAG: /* App */8,
      _0: {
        TAG: /* Var */2,
        _0: "h"
      },
      _1: {
        TAG: /* CstI */0,
        _0: 1
      }
    },
    _2: {
      TAG: /* App */8,
      _0: {
        TAG: /* Var */2,
        _0: "h"
      },
      _1: {
        TAG: /* CstI */0,
        _0: 0
      }
    }
  }
};

var fact = {
  TAG: /* Let */9,
  _0: "fac",
  _1: {
    TAG: /* Fun */7,
    _0: "n",
    _1: {
      TAG: /* If */3,
      _0: {
        TAG: /* Leq */6,
        _0: {
          TAG: /* Var */2,
          _0: "n"
        },
        _1: {
          TAG: /* CstI */0,
          _0: 0
        }
      },
      _1: {
        TAG: /* CstI */0,
        _0: 1
      },
      _2: {
        TAG: /* Mul */5,
        _0: {
          TAG: /* Var */2,
          _0: "n"
        },
        _1: {
          TAG: /* App */8,
          _0: {
            TAG: /* Var */2,
            _0: "fac"
          },
          _1: {
            TAG: /* Add */4,
            _0: {
              TAG: /* Var */2,
              _0: "n"
            },
            _1: {
              TAG: /* CstI */0,
              _0: -1
            }
          }
        }
      }
    }
  },
  _2: {
    TAG: /* App */8,
    _0: {
      TAG: /* Var */2,
      _0: "fac"
    },
    _1: {
      TAG: /* CstI */0,
      _0: 5
    }
  }
};

var more_fact = {
  TAG: /* Let */9,
  _0: "facc",
  _1: {
    TAG: /* Fun */7,
    _0: "m",
    _1: {
      TAG: /* Fun */7,
      _0: "n",
      _1: {
        TAG: /* If */3,
        _0: {
          TAG: /* Leq */6,
          _0: {
            TAG: /* Var */2,
            _0: "n"
          },
          _1: {
            TAG: /* CstI */0,
            _0: 0
          }
        },
        _1: {
          TAG: /* Var */2,
          _0: "m"
        },
        _2: {
          TAG: /* App */8,
          _0: {
            TAG: /* App */8,
            _0: {
              TAG: /* Var */2,
              _0: "facc"
            },
            _1: {
              TAG: /* Var */2,
              _0: "m"
            }
          },
          _1: {
            TAG: /* Add */4,
            _0: {
              TAG: /* Var */2,
              _0: "n"
            },
            _1: {
              TAG: /* CstI */0,
              _0: -1
            }
          }
        }
      }
    }
  },
  _2: {
    TAG: /* Var */2,
    _0: "facc"
  }
};

var tests_1 = {
  hd: fact,
  tl: {
    hd: more_fact,
    tl: /* [] */0
  }
};

var tests = {
  hd: test0,
  tl: tests_1
};

function run_test(ts) {
  Belt_List.forEach(ts, (function (t) {
          console.log("Expr: " + toStringE(t));
          var inferred = check_expr(/* [] */0, t, 0);
          console.log(toString(inferred));
        }));
}

function run(param) {
  run_test(tests);
}

var Test = {
  test0: test0,
  fact: fact,
  more_fact: more_fact,
  tests: tests,
  run_test: run_test,
  run: run
};

run_test(tests);

exports.LvLetPoly = LvLetPoly;
exports.Test = Test;
/*  Not a pure module */
