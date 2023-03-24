from functools import reduce
import source

conj = source.expr_and
disj = source.expr_or
imp = source.expr_implies

udiv = source.expr_udiv
mul = source.expr_mul
plus = source.expr_plus
sub = source.expr_sub

slt = source.expr_slt
sle = source.expr_sle
eq = source.expr_eq

T = source.expr_true
F = source.expr_false


def get(file_name: str, func_name: str) -> source.Ghost[source.HumanVarName] | None:
    if file_name.endswith('.c'):
        file_name = file_name[:-len('.c')] + '.txt'
    if file_name in universe and func_name in universe[file_name]:
        return universe[file_name][func_name]
    return None


def conjs(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    # pyright is stupid, but mypy works it out (we only care about mypy)
    return reduce(source.expr_and, xs)  # pyright: ignore


def i32(n: int) -> source.ExprNumT:
    assert -0x8000_0000 <= n and n <= 0x7fff_ffff
    return source.ExprNum(source.type_word32, n)


def i32v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word32, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def i64v(name: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word64, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def i64(n: int) -> source.ExprNumT:
    assert -0x8000_0000_0000_0000 <= n and n <= 0x7fff_ffff_ffff_ffff
    return source.ExprNum(source.type_word64, n)


def g(name: str) -> source.ExprVarT[source.HumanVarName]:
    """ guard """
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=True, path=()))


i32ret = source.ExprVar(source.type_word32, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))

i64ret = source.ExprVar(source.type_word64, source.HumanVarName(
    source.HumanVarNameSpecial.RET, use_guard=False, path=()))


def sbounded(var: source.ExprVarT[source.HumanVarName], lower: source.ExprT[source.HumanVarName], upper: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    return conj(sle(lower, var), sle(var, upper))

# def assigned(var: source.ExprVarT[source.HumanVarName]):
#     return source.ExprAssigned(source.type_bool, var)


def lh(x: str) -> source.LoopHeaderName:
    return source.LoopHeaderName(source.NodeName(x))


lc = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('GhostAssertions'), path=(), use_guard=False))

Ch = source.TypeBitVec(6)
Set_Ch = source.TypeBitVec(64)
Ch_set_has = source.FunctionName('Ch_set_has')
MsgInfo = source.TypeBitVec(80)
Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(80)

lc_running_pd = source.FunctionName('lc_running_pd')
lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
lc_receive_oracle = source.FunctionName('lc_receive_oracle')

C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Maybe_Prod_Ch_MsgInfo_Just')
C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
C_msg_info_valid = source.FunctionName('C_msg_info_valid')

C_channel_valid = source.FunctionName('C_channel_valid')


def arg_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    return v


def ret_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    return v


universe = {
    "tests/all.txt": {
        # 3 <= i ==> a = 1
        # 3:w32 <=s i:w32 ==> a:w32 = 1:w32
        "tmp.undefined_var_with_loops": source.Ghost(
            loop_invariants={
                lh("5"): conj(imp(sle(i32(3), i32v("i")), eq(i32v("a"), i32(1))), sbounded(i32v("i"), i32(0), i32(5)))
            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.multiple_loops___fail_missing_invariant": source.Ghost(
            loop_invariants={
                # no need to think, i is always going to be less than 200, and
                # that's enough to prove no overflows
                lh('17'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('4'): sbounded(i32v('i'), i32(0), i32(200)),
                lh('8'): sbounded(i32v('i'), i32(0), i32(200)),

            },
            precondition=T,
            postcondition=T,
        ),

        "tmp.arith_sum": source.Ghost(
            loop_invariants={
                # 0 <= i <= n
                # s = i * (i - 1) / 2
                # i#assigned
                # s#assigned
                lh('5'): conjs(
                    sbounded(i32v('i'), i32(0), i32v('n')),
                    eq(i32v('s'), udiv(mul(i32v('i'), sub(i32v('i'), i32(1))), i32(2))),
                    g('i'),
                    g('s')),
            },
            precondition=sbounded(i32v('n'), i32(0), i32(100)),
            postcondition=eq(i32ret, udiv(
                mul(i32v('n'), sub(i32v('i'), i32(1))), i32(2))),
        ),

        "tmp.multiple_ret_incarnations___fail_missing_invariants": source.Ghost(
            loop_invariants={lh('5'): T},
            precondition=sle(i32(0), i32v('n')),
            postcondition=eq(i32ret, udiv(i32v('n'), i32(2))),
        ),

        "tmp.callee": source.Ghost(
            loop_invariants={},
            precondition=sle(i32v('a'), i32(100)),
            postcondition=eq(i32ret, plus(i32v('a'), i32(1)))
        ),

        "tmp.caller": source.Ghost(
            loop_invariants={},
            precondition=sbounded(i32v('b'), i32(-100), i32(100)),
            postcondition=eq(i32ret, mul(plus(i32v('b'), i32(1)), i32(2))))
    },

    "tests/libsel4cp_trunc.txt": {
        # protected_wp :: Ch -> MsgInfo -> WP MsgInfo
        # protected_wp ch mi prop lc = and
        #   [ lc_unhandled_ppcall lc == Just (ch,mi)
        #   , wf_MsgInfo mi
        #   , prop rv lc'
        #   ] where
        #   rv = fresh_variable
        #   lc' = lc
        #     { lc_unhandled_ppcall = Nothing
        #     }
        "libsel4cp.protected": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc, )),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, (
                       # unsigned int is i64??
                       source.ExprFunction(
                           Ch, C_channel_to_SMT_channel, (i64v('ch'), )),
                       source.ExprFunction(
                           MsgInfo, C_msg_info_to_SMT_msg_info, ()),
                   ))),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i64v('ch'), )),
            ),
            postcondition=conjs(
                eq(source.ExprFunction(source.type_bool, lc_running_pd, (arg_value(lc), )),
                   source.ExprFunction(source.type_bool, lc_running_pd, (ret_value(lc), ))),
                eq(source.ExprFunction(source.type_bool, lc_receive_oracle, (arg_value(lc), )),
                   source.ExprFunction(source.type_bool, lc_receive_oracle, (ret_value(lc), )))
                # Do this for every other attribute
                # for lc_unhandled_ppcall, make sure it's equal to nothing
            ),
        ),

        # notified_wp :: Ch -> WP ()
        # notified_wp ch prop lc = and
        #   [ ch `elem` lc_unhandled_notified lc
        #   , prop (Just ()) lc'
        #   ] where
        #   lc' = lc
        #     { lc_unhandled_notified = lc_unhandled_notified lc \\ S.singleton ch
        #     , lc_last_handled_notified = lc_last_handled_notified lc `union` S.singleton ch
        #     }
        "libsel4cp.notified": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                source.ExprFunction(source.type_bool, Ch_set_has, (
                    source.ExprFunction(Set_Ch, lc_unhandled_notified, (lc, )),
                    # unsigned int is i64??
                    source.ExprFunction(
                        Ch, C_channel_to_SMT_channel, (i64v('ch'), )),
                )),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i64v('ch'), )),
            ),
            postcondition=conjs(
                eq(source.ExprFunction(source.type_bool, lc_running_pd, (arg_value(lc), )),
                   source.ExprFunction(source.type_bool, lc_running_pd, (ret_value(lc), )))
                # Do this for every other attribute
                # the exceptions are lc_unhandled_notified and lc_last_handled_notified of course
            ),
        )
    }
}
