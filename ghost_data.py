from functools import reduce
from math import prod
from sys import platform
from typing import Callable
import source
from global_smt_variables import PLATFORM_CONTEXT_BIT_SIZE

conj = source.expr_and
disj = source.expr_or
imp = source.expr_implies

udiv = source.expr_udiv
mul = source.expr_mul
plus = source.expr_plus
sub = source.expr_sub

slt = source.expr_slt
sle = source.expr_sle
ule = source.expr_ule
eq = source.expr_eq
neg = source.expr_negate
neq = source.expr_neq
ite = source.expr_ite

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
    if len(xs) == 0:
        return T
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


lc = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('GhostAssertions'), path=(), use_guard=False))
lc_arb_1 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('lc_arbitrary_1'), path=(), use_guard=False))
lc_arb_2 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('lc_arbitrary_2'), path=(), use_guard=False))
lc_arb_3 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('lc_arbitrary_3'), path=(), use_guard=False))
lc_arb_4 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('lc_arbitrary_4'), path=(), use_guard=False))
# lc_err = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
#     source.HumanVarNameSubject('lc_arbitrary_err'), path=(), use_guard=False))
lc_err = source.ExprNum(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), 0xdead1c)

ghost_arb_1 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_1'), path=(), use_guard=False))
ghost_arb_2 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_2'), path=(), use_guard=False))
ghost_arb_3 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_3'), path=(), use_guard=False))
ghost_arb_4 = source.ExprVar(source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE), source.HumanVarName(
    source.HumanVarNameSubject('ghost_arbitrary_4'), path=(), use_guard=False))

# Ch = source.TypeBitVec(6)
# Set_Ch = source.TypeBitVec(64)
# Ch_set_has = source.FunctionName('Ch_set_has')
# MsgInfo = source.TypeBitVec(80)
# Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(80)
Prod_Ch_MsgInfo = source.TypeBitVec(86)

# lc_running_pd = source.FunctionName('lc_running_pd')
# lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
# lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
# lc_receive_oracle = source.FunctionName('lc_receive_oracle')

# C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
# Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Prod_Ch_MsgInfo_Just')
# C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
# C_msg_info_valid = source.FunctionName('C_msg_info_valid')

# C_channel_valid = source.FunctionName('C_channel_valid')

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
NextRecvEnumNotification = source.FunctionName('<NR_Notification>')
NextRecvEnumPPCall = source.FunctionName('<NR_PPCall>')
NextRecvEnumUnknown = source.FunctionName('<NR_Unknown>')

NextRecv_Notification: source.ExprT[source.HumanVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumNotification, [])
NextRecv_PPCall: source.ExprT[source.HumanVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumPPCall, [])
NextRecv_Unknown: source.ExprT[source.HumanVarName] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumUnknown, [])

NextRecvNotificationGet = source.FunctionName('NR_Notification.1')
NextRecvPPCallGet = source.FunctionName('NR_PPCall.1')

lc_running_pd = source.FunctionName('lc_running_pd')
lc_receive_oracle = source.FunctionName('lc_receive_oracle')
lc_unhandled_notified = source.FunctionName('lc_unhandled_notified')
lc_last_handled_notified = source.FunctionName('lc_last_handled_notified')
lc_unhandled_ppcall = source.FunctionName('lc_unhandled_ppcall')
lc_unhandled_reply = source.FunctionName('lc_unhandled_reply')
lc_last_handled_reply = source.FunctionName('lc_last_handled_reply')

Prod_Ch_MsgInfo_Nothing = source.FunctionName('Prod_Ch_MsgInfo_Nothing')
Prod_Ch_MsgInfo_fn = source.FunctionName('Prod_Ch_MsgInfo')
MsgInfo_Nothing = source.FunctionName('MsgInfo_Nothing')


C_channel_to_SMT_channel = source.FunctionName('C_channel_to_SMT_channel')
Maybe_Prod_Ch_MsgInfo_Just = source.FunctionName('Prod_Ch_MsgInfo_Just')
MsgInfo_Just = source.FunctionName('MsgInfo_Just')
MsgInfo_Just_1 = source.FunctionName('MsgInfo_Just.1')

MI = source.FunctionName('MI')

Prod_Ch_MsgInfo_fst = source.FunctionName('Prod_Ch_MsgInfo.fst')
Prod_Ch_MsgInfo_snd = source.FunctionName('Prod_Ch_MsgInfo.snd')

C_msg_info_to_SMT_msg_info = source.FunctionName('C_msg_info_to_SMT_msg_info')
C_msg_info_valid = source.FunctionName('C_msg_info_valid')
C_channel_valid = source.FunctionName('C_channel_valid')

# constructor for platform context
PlatformContext_LC = source.FunctionName('LC')
PlatformContext = source.TypeBitVec(PLATFORM_CONTEXT_BIT_SIZE)


def word_cast(v: source.ExprT[source.VarNameKind], target_size: int) -> source.ExprT[source.VarNameKind]:
    assert isinstance(v.typ, source.TypeBitVec)
    assert v.typ.size <= target_size, "use extract, with meaningful guard"
    return source.ExprOp(source.TypeBitVec(target_size), operator=source.Operator.WORD_CAST, operands=(v, ))

# def mk_prod_msg_info(fst, snd):
#     return source.ExprFunction()


def mi_zeroed() -> source.ExprT[source.HumanVarName]:
    return source.ExprFunction(MsgInfo, MI, [source.ExprNum(source.type_word52, 0), source.ExprNum(source.type_word12, 0)])


mi_err: source.ExprT[source.HumanVarName]
mi_err = source.ExprFunction(MsgInfo, MI, [source.ExprNum(
    source.type_word52, 0xd), source.ExprNum(source.type_word12, 0xd)])


def arg_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    assert False, 'use arbitrary'
    return v


def ret_value(v: source.ExprVarT[source.VarNameKind]) -> source.ExprVarT[source.VarNameKind]:
    return v


def mkeq(fn_name: source.FunctionName, ty: source.Type, arg_lc: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    return eq(source.ExprFunction(ty, fn_name, arguments=(arg_lc,)),
              source.ExprFunction(ty, fn_name, arguments=(ret_value(lc),)))


NR_Notification = source.FunctionName('NR_Notification')
NR_Unknown = source.FunctionName('NR_Unknown')

Ch_empty_fn: source.ExprT[source.HumanVarName] = source.ExprFunction(
    Set_Ch, Ch_set_empty, ())


def hname(name: str, ty: source.Type) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(ty, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=False, path=()))


def wf_MsgInfo(msginfo: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
    """
    This well formedness is implied because of the way the label and the count
    is encoded (52 bits for the label, 12 bits for the rest).
    """
    return T

# data PlatformContext = LC
#   { ci :: PlatformInvariants
#   , lc_running_pd :: PD
#   , lc_receive_oracle :: NextRecv
#   , lc_unhandled_notified :: Set Ch
#   , lc_last_handled_notified :: Set Ch
#   , lc_unhandled_ppcall :: Maybe (Ch, MsgInfo)
#   , lc_unhandled_reply :: Maybe MsgInfo
#   , lc_last_handled_reply :: Maybe MsgInfo
#   }


def platform_context_update(
    base_lc: source.ExprT[source.HumanVarName],
    *,
    lc_running_pd_val: source.ExprT[source.HumanVarName] | None = None,
    lc_receive_oracle_val: source.ExprT[source.HumanVarName] | None = None,
    lc_unhandled_notified_val: source.ExprT[source.HumanVarName] | None = None,
    lc_last_handled_notified_val: source.ExprT[source.HumanVarName] | None = None,
    lc_unhandled_ppcall_val: source.ExprT[source.HumanVarName] | None = None,
    lc_unhandled_reply_val: source.ExprT[source.HumanVarName] | None = None,
    lc_last_handled_reply_val: source.ExprT[source.HumanVarName] | None = None,
) -> source.ExprT[source.HumanVarName]:
    """
    Copies every field from base_lc, apart from the specified fields.

    This matches the update syntax in haskell. When we write

        lc' = lc { f1: v1, f2: v2, ... },

    we use

        lc' platform_context_update(lc, f1=v1, f2=v2, ...).

    """
    fields = [lc_running_pd, lc_receive_oracle, lc_unhandled_notified,
              lc_last_handled_notified, lc_unhandled_ppcall, lc_unhandled_reply, lc_last_handled_reply]
    vals = [lc_running_pd_val, lc_receive_oracle_val, lc_unhandled_notified_val, lc_last_handled_notified_val,
            lc_unhandled_ppcall_val, lc_unhandled_reply_val, lc_last_handled_reply_val]
    typs = [PD, NextRecv, Set_Ch, Set_Ch,
            Maybe_Prod_Ch_MsgInfo, Maybe_MsgInfo, Maybe_MsgInfo]

    arguments: list[source.ExprT[source.HumanVarName]] = []

    for i, (field, val, typ) in enumerate(zip(fields, vals, typs)):
        new_value: source.ExprT[source.HumanVarName]
        if val is None:
            new_value = source.ExprFunction(typ, field, [base_lc])
        else:
            assert val.typ == typ, f"argument {i+1} (1-based), namely {field}, should have typ {typ}, got {val.typ}"
            new_value = val

        arguments.append(new_value)

    # needs the arguments to be in the same order
    return source.ExprFunction(PlatformContext, PlatformContext_LC, arguments)


# sel4cp_correspondence_recv_wp :: WP MsgInfo
# sel4cp_correspondence_recv_wp prop lc = and
#   [ lc_receive_oracle lc /= NR_Unknown
#   , lc_receive_oracle lc /= NR_Notification S.empty
#   , lc_unhandled_notified lc == S.empty
#   , lc_unhandled_ppcall lc == Nothing
#   , lc_unhandled_reply lc == Nothing
#   , wf_MsgInfo rv
#   , prop (Just rv) lc'
#   ] where
#   rv = case lc_receive_oracle lc of
#     NR_Notification notis -> MI 0 0
#     NR_PPCall (_, mi) -> mi
#     _ -> error "sel4cp_correspondence_recv_wp: Precondition violation in rv."
#   lc' = case lc_receive_oracle lc of
#     NR_Notification notis -> lc
#       { lc_receive_oracle = NR_Unknown
#       , lc_unhandled_notified = notis
#       }
#     NR_PPCall ppc -> lc
#       { lc_receive_oracle = NR_Unknown
#       , lc_unhandled_ppcall = Just ppc
#       }
#     _ -> error "sel4cp_correspondence_recv_wp: Precondition violation."
def recv_postcondition(rv: source.ExprT[source.HumanVarName], arg_lc: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:

    def rv_when_notification(_: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return mi_zeroed()

    def rv_when_ppcall(prod_ch_msginfo: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return source.ExprFunction(MsgInfo, Prod_Ch_MsgInfo_snd, [prod_ch_msginfo])

    def rv_when_unknown() -> source.ExprT[source.HumanVarName]:
        return mi_err

    def lc_when_notification(notis: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_notified_val=notis,
        )

    def lc_when_ppcall(prod_ch_msginfo: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_ppcall_val=source.ExprFunction(
                Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [prod_ch_msginfo])
        )

    def lc_when_unknown() -> source.ExprT[source.HumanVarName]:
        return lc_err

    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, [arg_lc])

    rv = NextRecv_case(oracle, rv_when_notification,
                       rv_when_ppcall, rv_when_unknown)
    lc = NextRecv_case(oracle, lc_when_notification,
                       lc_when_ppcall, lc_when_unknown)

    return conjs(
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [i64ret]),
            rv
        ),
        eq(lc, arg_lc)
    )


# data NextRecv
#   = NR_Notification (Set Ch)
#   | NR_PPCall (Ch, MsgInfo)
#   | NR_Unknown
def NextRecv_case(
        nr: source.ExprT[source.HumanVarName],
        NR_Notification: Callable[[source.ExprT[source.HumanVarName]], source.ExprT[source.HumanVarName]],
        NR_PPCall: Callable[[source.ExprT[source.HumanVarName]], source.ExprT[source.HumanVarName]],
        NR_Unknown: Callable[[], source.ExprT[source.HumanVarName]]) -> source.ExprT[source.HumanVarName]:
    """
    Relies on the assumption that every constructor is distinct. This is
    established in gen.py
    """

    set_ch = source.ExprFunction(Set_Ch, NextRecvNotificationGet, [nr])

    # next_recv_ppcall = source.ExprFunction(Prod_Ch_MsgInfo,
    prod_ch_msginfo = source.ExprFunction(
        Prod_Ch_MsgInfo, NextRecvPPCallGet, [nr])

    constructor = source.ExprFunction(NextRecvEnum, NextRecvEnumGet, [nr])

    is_notif = eq(constructor, NextRecv_Notification)
    is_ppcall = eq(constructor, NextRecv_PPCall)
    # this one is deduced (all the constructors are distinct)
    is_unknown = eq(constructor, NextRecv_Unknown)

    return ite(is_notif, NR_Notification(set_ch), ite(is_ppcall, NR_PPCall(prod_ch_msginfo), NR_Unknown()))

# sel4cp_correspondence_replyrecv_wp :: MsgInfo -> WP MsgInfo
# sel4cp_correspondence_replyrecv_wp reply_tag prop lc = and
#   [ lc_receive_oracle lc /= NR_Unknown
#   , lc_receive_oracle lc /= NR_Notification S.empty
#   , wf_MsgInfo reply_tag
#   , lc_unhandled_notified lc == S.empty
#   , lc_unhandled_ppcall lc == Nothing
#   , lc_unhandled_reply lc /= Nothing
#   , wf_MsgInfo rv
#   , prop (Just rv) lc'
#   ] where
#   rv = case lc_receive_oracle lc of
#     NR_Notification notis -> MI 0 0
#     NR_PPCall (_, mi) -> mi
#     _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation in rv."
#   lc' = case lc_receive_oracle lc of
#     NR_Notification notis -> lc
#       { lc_receive_oracle = NR_Unknown
#       , lc_unhandled_notified = notis
#       , lc_unhandled_reply = Nothing
#       , lc_last_handled_reply = lc_unhandled_reply lc
#       }
#     NR_PPCall ppc -> lc
#       { lc_receive_oracle = NR_Unknown
#       , lc_unhandled_ppcall = Just ppc
#       , lc_unhandled_reply = Nothing
#       , lc_last_handled_reply = lc_unhandled_reply lc
#       }
#     _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation."


def replyrecv_postcondition(rv: source.ExprT[source.HumanVarName], arg_lc: source.ExprVarT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:

    # NR_Notification notis -> lc
    #   { lc_receive_oracle = NR_Unknown
    #   , lc_unhandled_notified = notis
    #   , lc_unhandled_reply = Nothing
    #   , lc_last_handled_reply = lc_unhandled_reply lc
    #   }
    def lc_when_notification(notis: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_notified_val=notis,
            lc_unhandled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, MsgInfo_Nothing, ()),
            lc_last_handled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [arg_lc]),
        )

    # NR_PPCall ppc -> lc
    #   { lc_receive_oracle = NR_Unknown
    #   , lc_unhandled_ppcall = Just ppc
    #   , lc_unhandled_reply = Nothing
    #   , lc_last_handled_reply = lc_unhandled_reply lc
    #   }
    def lc_when_ppcall(ppc: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return platform_context_update(
            arg_lc,
            lc_receive_oracle_val=source.ExprFunction(
                NextRecv, NR_Unknown, []),
            lc_unhandled_ppcall_val=source.ExprFunction(
                Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [ppc]),
            lc_unhandled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, MsgInfo_Nothing, []),
            lc_last_handled_reply_val=source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [arg_lc]),
        )

    # _ ->  error "sel4cp_correspondence_replyrecv_wp: Precondition violation."
    def lc_when_unknown() -> source.ExprT[source.HumanVarName]:
        return lc_err

    # lc' = case lc_receive_oracle lc of ...
    oracle = source.ExprFunction(NextRecv, lc_receive_oracle, [arg_lc])
    lc_prime = NextRecv_case(oracle, lc_when_notification,
                             lc_when_ppcall, lc_when_unknown)

    # lc case DONE

    # NR_Notification notis -> MI 0 0
    def rv_when_notification(_: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return mi_zeroed()

    # NR_PPCall (_, mi) -> mi
    def rv_when_ppcall(prod_ch_msginfo: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return source.ExprFunction(MsgInfo, Prod_Ch_MsgInfo_snd, [prod_ch_msginfo])

    # _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation in rv."
    def rv_when_unknown() -> source.ExprT[source.HumanVarName]:
        return mi_err

    rv = NextRecv_case(oracle, rv_when_notification,
                       rv_when_ppcall, rv_when_unknown)
    # rv case DONE

    return conjs(
        eq(ret_value(lc), lc_prime),
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [i64ret]),
            rv
        )
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
                eq(lc, plus(ghost_arb_2, num(1, PLATFORM_CONTEXT_BIT_SIZE))),
                eq(i32ret, i32v('a')),
            ),
        ),
        "tmp.use_modified_ghost_using_prelude": source.Ghost(
            loop_invariants={},
            precondition=conjs(
                eq(lc, ghost_arb_3),
            ),
            postcondition=conjs(
                eq(lc, plus(ghost_arb_3, num(1, PLATFORM_CONTEXT_BIT_SIZE))),
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
                    eq(lc, plus(ghost_arb_1, word_cast(
                        i32v('i'), PLATFORM_CONTEXT_BIT_SIZE))),
                ),
            },
            precondition=eq(lc, ghost_arb_1),
            postcondition=eq(lc, plus(ghost_arb_1, word_cast(
                i32(10), PLATFORM_CONTEXT_BIT_SIZE))),
        )

    },

    "tests/libsel4cp_trunc.txt": {
        # This function has no way of verifying. It modifies the sel4cp ghost
        # state out of the blue.
        #
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
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [
                       source.ExprFunction(Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_fn, (
                           # unsigned int is i64??
                           source.ExprFunction(
                               Ch, C_channel_to_SMT_channel, (i64v('ch'), )),
                           source.ExprFunction(
                               MsgInfo, C_msg_info_to_SMT_msg_info, (i64v('msginfo'), )),
                       ))
                   ])),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i64v('ch'), )),
            ),
            postcondition=conjs(
                mkeq(lc_running_pd, PD, lc_arb_1),
                mkeq(lc_receive_oracle, NextRecv, lc_arb_1),
                mkeq(lc_unhandled_notified, Set_Ch, lc_arb_1),
                mkeq(lc_last_handled_notified, Set_Ch, lc_arb_1),
                mkeq(lc_unhandled_reply, Maybe_MsgInfo, lc_arb_1),
                mkeq(lc_last_handled_reply, Maybe_MsgInfo, lc_arb_1),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc_arb_1,)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, ())),
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
                eq(lc, lc_arb_2),
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
                mkeq(lc_running_pd, PD, lc_arb_2),
                mkeq(lc_receive_oracle, NextRecv, lc_arb_2),
                # lc_unhandled_notified
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (ret_value(lc),)),
                   source.ExprFunction(Set_Ch, Ch_set_remove,
                                       (source.ExprFunction(Set_Ch,  lc_unhandled_notified, (lc_arb_2,), ),
                                        source.ExprFunction(
                                            Ch, C_channel_to_SMT_channel, (i64v('ch'),))
                                        )
                                       )
                   ),
                # lc_last_handled_notified
                eq(source.ExprFunction(Set_Ch, lc_last_handled_notified, (ret_value(lc),)),
                    source.ExprFunction(Set_Ch, Ch_set_add, [
                        source.ExprFunction(
                            Set_Ch, lc_last_handled_notified, (lc_arb_2,)),
                        source.ExprFunction(
                            Ch, C_channel_to_SMT_channel, (i64v('ch'),))
                    ])
                   ),
                mkeq(lc_unhandled_ppcall, Maybe_Prod_Ch_MsgInfo, lc_arb_2),
                mkeq(lc_unhandled_reply, Maybe_MsgInfo, lc_arb_2),
                mkeq(lc_last_handled_reply, Maybe_MsgInfo, lc_arb_2)

                # Do this for every other attribute
                # the exceptions are lc_unhandled_notified and lc_last_handled_notified of course
            ),
        ),
        "libsel4cp.seL4_Recv": source.Ghost(
            precondition=conjs(
                eq(lc, lc_arb_3),
                neq(source.ExprFunction(NextRecv, lc_receive_oracle, (lc,)),
                    source.ExprFunction(NextRecv, NR_Unknown, ())),
                neq(source.ExprFunction(NextRecv, lc_receive_oracle, (lc,)),
                    source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,))),
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (lc,)),
                   Ch_empty_fn),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc,)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
                eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (lc,)),
                   source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])),
                eq(source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, (lc,)),
                   source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, [])),
                # wf_MsgInfo()
                # TODO: wf_MsgInfo rv
                #
                # Note that rv shouldn't be i64ret!! we have to do a whole
                # case split (NextRecv_case), as a precondition
            ),
            postcondition=recv_postcondition(
                source.ExprFunction(MsgInfo, source.FunctionName(
                    'C_msg_info_to_SMT_msg_info'), [i64ret]),
                lc_arb_3),
            loop_invariants={}
        ),
        "libsel4cp.seL4_ReplyRecv": source.Ghost(
            precondition=conjs(
                eq(lc, lc_arb_4),
                neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (lc,)),
                       source.ExprFunction(NextRecv, NR_Unknown, []))),
                neg(eq(source.ExprFunction(NextRecv, lc_receive_oracle, (lc,)),
                       source.ExprFunction(NextRecv, NR_Notification, (Ch_empty_fn,)))),
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (lc,)),
                   Ch_empty_fn),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc,)),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_Nothing, [])),
                neg(eq(source.ExprFunction(Maybe_MsgInfo, lc_unhandled_reply, (lc,)),
                       source.ExprFunction(Maybe_MsgInfo, MsgInfo_Nothing, []))),
                # TODO: wf_MsgInfo rv
            ),
            postcondition=replyrecv_postcondition(
                source.ExprFunction(MsgInfo, source.FunctionName(
                    'C_msg_info_to_SMT_msg_info'), [i64ret]),
                lc_arb_4,
            ),
            loop_invariants={}
        )
    }
}
