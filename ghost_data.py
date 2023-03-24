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
neg = source.expr_negate

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


def num(n: int, bvsize: int) -> source.ExprT[source.VarNameKind]:
    assert n <= 2 ** bvsize
    return source.ExprNum(source.TypeBitVec(bvsize), n)


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
lc_arb_1 = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('lc_arbitrary_1'), path=(), use_guard=False))

ghost_arb_1 = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_1'), path=(), use_guard=False))
ghost_arb_2 = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_2'), path=(), use_guard=False))
ghost_arb_3 = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_3'), path=(), use_guard=False))
ghost_arb_4 = source.ExprVar(source.TypeBitVec(471), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_4'), path=(), use_guard=False))

Ch = source.TypeBitVec(6)
PD = source.TypeBitVec(6)
NextRecv = source.TypeBitVec(88)
NextRecvEnum = source.TypeBitVec(2)
Set_Ch = source.TypeBitVec(64)
MsgInfo = source.TypeBitVec(80)
Prod_Ch_MsgInfo = source.TypeBitVec(86)
Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(87)
Maybe_MsgInfo = source.TypeBitVec(81)

Ch_set_empty = source.FunctionName('Ch_set_empty')
Ch_set_has = source.FunctionName('Ch_set_has')
Ch_set_add = source.FunctionName("Ch_set_add")
Ch_set_remove = source.FunctionName("Ch_set_remove")

NextRecvEnumGet = source.FunctionName('NextRecv.<>')
NextRecvEnumNotification = source.FunctionName('<Notification>')
NextRecvEnumPPCall = source.FunctionName('<PPCall>')

NextRecvNotificationGet = source.FunctionName('Notification.1')
NextRecvPPCallGet = source.FunctionName('PPCall.1')

lc_running_pd = source.FunctionName('lc_running_pd')
lc_receive_oracle = source.FunctionName('lc_receive_oracle')
lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
lc_last_handled_notified = source.FunctionName('lc_last_handled_notified')
lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
lc_unhandled_reply = source.FunctionName('lc_unhandled_reply')
lc_last_handled_reply = source.FunctionName('lc_last_handled_reply')

Prod_Ch_MsgInfo_Nothing = source.FunctionName('Prod_Ch_MsgInfo_Nothing')
MsgInfo_Nothing = source.FunctionName('MsgInfo_Nothing')


C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Maybe_Prod_Ch_MsgInfo_Just')
MsgInfo_Just = source.FunctionName('MsgInfo_Just')
MsgInfo_Just_1 = source.FunctionName('MsgInfo_Just.1')

MI = source.FunctionName('MI')

Prod_Ch_MsgInfo_fst = source.FunctionName('Prod_Ch_MsgInfo.fst')
Prod_Ch_MsgInfo_snd = source.FunctionName('Prod_Ch_MsgInfo.snd')

C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
C_msg_info_valid = source.FunctionName('C_msg_info_valid')
C_channel_valid = source.FunctionName('C_channel_valid')


def mi_zeroed() -> source.ExprT[source.HumanVarName]:
    return source.ExprFunction(MsgInfo, MI, [source.ExprNum(source.type_word64, 0), source.ExprNum(source.type_word16, 0)])


def arg_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    return v


def ret_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    return v


def mkeq(fn_name: source.FunctionName, ty: source.Type) -> source.ExprT[source.HumanVarName]:
    return eq(source.ExprFunction(ty, fn_name, arguments=(arg_value(lc),)),
              source.ExprFunction(ty, fn_name, arguments=(ret_value(lc),)))


NR_Notification = source.FunctionName('Notification')
NR_Unknown = source.FunctionName('Unknown')

Ch_empty_fn: source.ExprT[source.HumanVarName] = source.ExprFunction(
    Set_Ch, Ch_set_empty, ())


def hname(name: str, ty: source.Type) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(ty, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))
def word_cast(v: source.ExprT[source.VarNameKind], target_size: int) -> source.ExprT[source.VarNameKind]:
    assert isinstance(v.typ, source.TypeBitVec)
    assert v.typ.size <= target_size, "use extract, with meaningful guard"
    return source.ExprOp(source.TypeBitVec(target_size), operator=source.Operator.WORD_CAST, operands=(v, ))

# def mk_prod_msg_info(fst, snd):
#     return source.ExprFunction()



def wf_MsgInfo() -> source.ExprT[source.HumanVarName]:
    label_fn_name = source.FunctionName('label')
    count_fn_name = source.FunctionName('count')
    just_val = source.ExprFunction(
        Maybe_MsgInfo, MsgInfo_Just, (arg_value(lc),))
    label = source.ExprFunction(source.type_word64, label_fn_name, [just_val])
    count = source.ExprFunction(source.type_word16, count_fn_name, [just_val])

    label_maxval = source.ExprNum(source.type_word64, 0xffffffffffff)
    count_maxval = source.ExprNum(source.type_word16, 127)

    # TODO: is this correct?
    return conjs(
        sle(label, label_maxval),
        sle(count, count_maxval)
    )


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
            postcondition=eq(i32ret, mul(plus(i32v('b'), i32(1)), i32(2)))),

        "tmp.caller2": source.Ghost(
            loop_invariants={},
            precondition=sbounded(i32v('b'), i32(-99), i32(99)),
            postcondition=eq(i32ret, mul(plus(i32v('b'), i32(2)), i32(2)))),

        "tmp.caller3": source.Ghost(
            loop_invariants={
                lh('6'): conjs(
                    sbounded(i32v('i'), i32(0), i32(20)),
                    g('i'),
                    g('Mem'),
                    g('PMS'),
                    g('HTD'),
                    g('GhostAssertions'),
                )
            },
            precondition=sbounded(i32v('b'), i32(-100), i32(100)),
            postcondition=eq(i32ret, plus(i32v('b'), i32(20)))),

        "tmp.does_not_change_ghost_using_prelude": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                eq(lc, ghost_arb_1)
            ),
            postcondition=conjs(
                eq(lc, ghost_arb_1)
            ),
        ),
        "tmp.increments_ghost_using_prelude___fail": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                eq(lc, ghost_arb_2),
                eq(i32v('a'), i32(1)),
            ),
            postcondition=conjs(
                eq(lc, plus(ghost_arb_2, num(1, 471))),
                eq(i32ret, i32v('a')),
            ),
        ),
        "tmp.use_modified_ghost_using_prelude": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                eq(lc, ghost_arb_3),
            ),
            postcondition=conjs(
                eq(lc, plus(ghost_arb_3, num(1, 471))),
            ),
        ),
        "tmp.use_modified_ghost_using_prelude_x10": source.Ghost(
            loop_invariants={
                # lh('5'): ,
                lh('5'): conjs(
                    g('i'),
                    g('HTD'),
                    g('GhostAssertions'),
                    g('PMS'),
                    g('Mem'),
                    sbounded(i32v('i'), i32(0), i32(10)),
                    eq(lc, plus(ghost_arb_1, word_cast(i32v('i'), 471))),
                ),
            },
            precondition=eq(lc, ghost_arb_1),
            postcondition=eq(lc, plus(ghost_arb_1, word_cast(i32(10), 471))),
        )

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
                eq(lc, lc_arb_1),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc, )),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, (
                       # unsigned int is i64??
                       source.ExprFunction(Prod_Ch_MsgInfo, source.FunctionName('Prod_Ch_MsgInfo'), (
                           source.ExprFunction(
                               Ch, C_channel_to_SMT_channel, (i64v('ch'), )),
                           source.ExprFunction(
                               MsgInfo, C_msg_info_to_SMT_msg_info, (i64v('msginfo'), )),
                       )),
                   ))),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i64v('ch'), )),
            ),
            postcondition=conjs(
                mkeq(lc_running_pd, PD),
                mkeq(lc_receive_oracle, NextRecv),
                mkeq(lc_unhandled_notified,  Set_Ch),
                mkeq(lc_last_handled_notified, Set_Ch),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (ret_value(lc),)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, ())),
                mkeq(lc_unhandled_reply, Maybe_MsgInfo),
                mkeq(lc_last_handled_reply, Maybe_MsgInfo),
                # eq(source.ExprFunction(typ
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
                mkeq(lc_running_pd, PD),
                mkeq(lc_receive_oracle, NextRecv),
                # lc_unhandled_notified
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (ret_value(lc),)),
                   source.ExprFunction(Set_Ch, Ch_set_remove,
                                       (source.ExprFunction(Set_Ch,  lc_unhandled_notified, (arg_value(lc),), ),
                                        source.ExprFunction(
                                            Ch, C_channel_to_SMT_channel, (i64v('ch'),))
                                        )
                                       )
                   ),
                # lc_last_handled_notified
                eq(source.ExprFunction(Set_Ch, lc_last_handled_notified, (ret_value(lc),)),
                    source.ExprFunction(Set_Ch, Ch_set_add, [
                        source.ExprFunction(
                            Set_Ch, lc_last_handled_notified, (arg_value(lc),)),
                        source.ExprFunction(
                            Ch, C_channel_to_SMT_channel, (i64v('ch'),))
                    ])
                   ),
                mkeq(lc_unhandled_ppcall, Maybe_Prod_Ch_MsgInfo),
                mkeq(lc_unhandled_reply, Maybe_MsgInfo),
                mkeq(lc_last_handled_reply, Maybe_MsgInfo)

                # Do this for every other attribute
                # the exceptions are lc_unhandled_notified and lc_last_handled_notified of course
            ),
        ),
        "libsel4cp.seL4_Recv": source.Ghost(
            precondition=conjs(
                eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),)),
                   source.ExprFunction(NextRecv, NR_Unknown, ())),
                eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),)),
                   source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,))),
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (arg_value(lc),)),
                   Ch_empty_fn),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (arg_value(lc),)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
                eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (arg_value(lc),)),
                   source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])),
                eq(source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, (arg_value(lc),)),
                   source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])),
            ),
            postcondition=T,
            loop_invariants={}
        ),
        "libsel4cp.seL4_ReplyRecv": source.Ghost(
            precondition=conjs(
                neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),)),
                       source.ExprFunction(NextRecv, NR_Unknown, []))),
                neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),)),
                    source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,)))),
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (arg_value(lc),)),
                   Ch_empty_fn),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (arg_value(lc),)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
                neg(eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (arg_value(lc),)),
                       source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, []))),
            ),
            postcondition=T,
            loop_invariants={}
        )
    }
}


def recv_postcondition(rv: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),))
    oracle_ret = source.ExprFunction(
        NextRecv, lc_receive_oracle, (ret_value(lc),))
    nextenum: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumGet, (oracle,))
    nextnotification: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumNotification, [])
    nextppcall: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumPPCall, [])

    # when_notification_rv = source.ExprFunction(MsgInfo, MsgInfo)
    # when_ppcall_rv = source.ExprFunction()

    # when_notification_lc
    # when_ppcall_lc
    when_notification = source.expr_implies(eq(nextenum, nextnotification), T)
    when_ppcall = source.expr_implies(eq(nextenum, nextppcall), T)

    return conjs(when_notification, when_ppcall)


def replyrecv_postcondition(rv: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, (arg_value(lc),))
    oracle_ret = source.ExprFunction(
        NextRecv, lc_receive_oracle, (ret_value(lc),))

    nextenum: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumGet, (oracle,))
    nextnotificationenum: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumNotification, [])
    nextppcallenum: source.ExprT[source.HumanVarName] = source.ExprFunction(
        NextRecvEnum, NextRecvEnumPPCall, [])

    nextnotification = source.ExprFunction(
        Set_Ch, NextRecvNotificationGet, [oracle])
    nextppcall = source.ExprFunction(
        Prod_Ch_MsgInfo, NextRecvPPCallGet, [oracle])

    when_notification_rv = eq(rv, mi_zeroed())

    when_ppcall_rv = eq(rv, source.ExprFunction(
        MsgInfo, Prod_Ch_MsgInfo_snd, [nextppcall]))

    when_notification_lc = conjs(
        eq(
            oracle_ret,
            source.ExprFunction(NextRecv, NR_Unknown, []),
        ),
        eq(
            source.ExprFunction(
                NextRecv, lc_unhandled_notified, (ret_value(lc),)),
            source.ExprFunction(
                Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [nextnotification])
        ),
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, (ret_value(lc),)),
            source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])
        ),
        mkeq(lc_last_handled_reply, Maybe_MsgInfo)
    )
    when_ppcall_lc = conjs(
        eq(
            oracle_ret,
            source.ExprFunction(NextRecv, NR_Unknown, []),
        ),
        eq(
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                lc_unhandled_ppcall, (ret_value(lc),)),
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [
                nextppcall
            ])
        ),
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, (arg_value(lc),)),
            source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])
        ),
        mkeq(lc_last_handled_reply, Maybe_MsgInfo)
    )
    when_notification = source.expr_implies(eq(nextenum, nextnotificationenum), conjs(
        when_notification_rv, when_notification_lc))
    when_ppcall = source.expr_implies(
        eq(nextenum, nextppcallenum), conjs(when_ppcall_rv, when_ppcall_lc))
    return conjs(when_notification, when_ppcall)
