from functools import reduce
from math import prod
from sys import platform
from typing import Callable, Any
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


def ors(*xs: source.ExprT[source.VarNameKind]) -> source.ExprT[source.VarNameKind]:
    # pyright is stupid, but mypy works it out (we only care about mypy)
    if len(xs) == 0:
        return T
    return reduce(source.expr_or, xs)  # pyright: ignore


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


def charv(n: str) -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_word8, source.HumanVarName(source.HumanVarNameSubject(n), use_guard=False, path=()))


def char(n: int) -> source.ExprNumT:
    return source.ExprNum(source.type_word8, n)


def g(name: str) -> source.ExprVarT[source.HumanVarName]:
    """ guard """
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject(name), use_guard=True, path=()))


def htd_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('HTD'), use_guard=True, path=()))


def mem_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('Mem'), use_guard=True, path=()))


def pms_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('PMS'), use_guard=True, path=()))


def ghost_asserts_assigned() -> source.ExprVarT[source.HumanVarName]:
    return source.ExprVar(source.type_bool, source.HumanVarName(source.HumanVarNameSubject('GhostAssertions'), use_guard=True, path=()))


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


def coerce_varkind(e: source.ExprVarT[source.HumanVarName]) -> source.ExprVarT[source.ProgVarName]:
    return source.ExprVar(e.typ, source.ProgVarName(e.name.subject))


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
NextRecv = source.TypeBitVec(72)
NextRecvEnum = source.TypeBitVec(2)
Set_Ch = source.TypeBitVec(64)
MsgInfo = source.TypeBitVec(64)
Prod_Ch_MsgInfo = source.TypeBitVec(70)
Maybe_Prod_Ch_MsgInfo = source.TypeBitVec(71)
Maybe_MsgInfo = source.TypeBitVec(65)
Maybe_MsgInfoEnum = source.TypeBitVec(1)
SeL4_Ntfn = source.TypeBitVec(64)
Prod_MsgInfo_SeL4_Ntfn = source.TypeBitVec(128)

Ch_set_empty = source.FunctionName('Ch_set_empty')
Ch_set_has = source.FunctionName('Ch_set_has')
Ch_set_add = source.FunctionName("Ch_set_add")
Ch_set_remove = source.FunctionName("Ch_set_remove")

NextRecvEnumGet = source.FunctionName('NextRecv.<>')
NextRecvEnumNotification = source.FunctionName('<NR_Notification>')
NextRecvEnumPPCall = source.FunctionName('<NR_PPCall>')
NextRecvEnumUnknown = source.FunctionName('<NR_Unknown>')

Maybe_MsgInfoEnumGet = source.FunctionName('Maybe_MsgInfo.<>')
Maybe_MsgInfoEnumJust = source.FunctionName('<MsgInfo_Just>')
Maybe_MsgInfoEnumNothing = source.FunctionName('<MsgInfo_Nothing>')

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
    lc_prime = NextRecv_case(oracle, lc_when_notification,
                             lc_when_ppcall, lc_when_unknown)

    mem = source.ExprVar(source.type_mem, source.HumanVarName(
        source.HumanVarNameSubject('Mem'), path=(), use_guard=False))
    gbadge: source.ExprT[source.HumanVarName] = source.ExprFunction(
        source.type_word61, source.FunctionName('badge'), [])
    mem_condition: source.ExprT[source.HumanVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName("mem-acc"), [mem, gbadge])

    recv_oracle_kernel: source.ExprT[source.HumanVarName] = source.ExprFunction(
        Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])
    recv_badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])

    return conjs(
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [i64ret]),
            rv
        ),
        eq(ret_value(lc), lc_prime),
        eq(mem_condition, recv_badge)
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

    recv_oracle_kernel: source.ExprT[source.HumanVarName] = source.ExprFunction(
        Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])
    recv_badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])
    mem = source.ExprVar(source.type_mem, source.HumanVarName(
        source.HumanVarNameSubject('Mem'), path=(), use_guard=False))
    gbadge: source.ExprT[source.HumanVarName] = source.ExprFunction(
        source.type_word61, source.FunctionName('badge'), [])
    mem_condition: source.ExprT[source.HumanVarName] = source.ExprFunction(
        source.type_word64, source.FunctionName("mem-acc"), [mem, gbadge])

    # NR_Notification notis -> MI 0 0
    def rv_when_notification(_: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return mi_zeroed()

    # NR_PPCall (_, mi) -> mi
    def rv_when_ppcall(prod_ch_msginfo: source.ExprT[source.HumanVarName]) -> source.ExprT[source.HumanVarName]:
        return source.ExprFunction(MsgInfo, Prod_Ch_MsgInfo_snd, [prod_ch_msginfo])

    # _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation in rv."
    def rv_when_unknown() -> source.ExprT[source.HumanVarName]:
        return mi_err

    # def mem_when_notification()

    rv = NextRecv_case(oracle, rv_when_notification,
                       rv_when_ppcall, rv_when_unknown)
    # rv case DONE

    return conjs(
        eq(ret_value(lc), lc_prime),
        eq(
            source.ExprFunction(
                MsgInfo, C_msg_info_to_SMT_msg_info, [i64ret]),
            rv
        ),
        eq(mem_condition, recv_badge)
    )


def handler_loop_node_name() -> str:
    return '3'


universe = {
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
            precondition_assumption=eq(
                coerce_varkind(lc),
                coerce_varkind(lc_arb_1)
            ),
            loop_invariants={},
            precondition=conjs(
                eq(lc, lc_arb_1),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (lc, )),
                   source.ExprFunction(Maybe_Prod_Ch_MsgInfo, Maybe_Prod_Ch_MsgInfo_Just, [
                       source.ExprFunction(Prod_Ch_MsgInfo, Prod_Ch_MsgInfo_fn, (
                           # unsigned int is i64??
                           source.ExprFunction(
                               Ch, C_channel_to_SMT_channel, (i32v('ch'), )),
                           source.ExprFunction(
                               MsgInfo, C_msg_info_to_SMT_msg_info, (i64v('msginfo'), )),
                       ))
                   ])),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i32v('ch'), )),
            ),
            postcondition=conjs(
                mkeq(lc_running_pd, PD, lc_arb_1),
                mkeq(lc_receive_oracle, NextRecv, lc_arb_1),
                mkeq(lc_unhandled_notified, Set_Ch, lc_arb_1),
                mkeq(lc_last_handled_notified, Set_Ch, lc_arb_1),
                mkeq(lc_unhandled_reply, Maybe_MsgInfo, lc_arb_1),
                mkeq(lc_last_handled_reply, Maybe_MsgInfo, lc_arb_1),
                eq(source.ExprFunction(Maybe_Prod_Ch_MsgInfo, lc_unhandled_ppcall, (ret_value(lc),)),
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
            precondition_assumption=eq(
                coerce_varkind(lc),
                coerce_varkind(lc_arb_2)
            ),
            precondition=conjs(
                eq(lc, lc_arb_2),
                source.ExprFunction(source.type_bool, Ch_set_has, (
                    source.ExprFunction(Set_Ch, lc_unhandled_notified, (lc, )),
                    # unsigned int is i64??
                    source.ExprFunction(
                        Ch, C_channel_to_SMT_channel, (i32v('ch'), )),
                )),
                source.ExprFunction(
                    source.type_bool, C_channel_valid, (i32v('ch'), )),
            ),
            postcondition=conjs(
                mkeq(lc_running_pd, PD, lc_arb_2),
                mkeq(lc_receive_oracle, NextRecv, lc_arb_2),
                # lc_unhandled_notified
                eq(source.ExprFunction(Set_Ch, lc_unhandled_notified, (ret_value(lc),)),
                   source.ExprFunction(Set_Ch, Ch_set_remove,
                                       (source.ExprFunction(Set_Ch,  lc_unhandled_notified, (lc_arb_2,), ),
                                        source.ExprFunction(
                                            Ch, C_channel_to_SMT_channel, (i32v('ch'),))
                                        )
                                       )
                   ),
                # lc_last_handled_notified
                eq(source.ExprFunction(Set_Ch, lc_last_handled_notified, (ret_value(lc),)),
                    source.ExprFunction(Set_Ch, Ch_set_add, [
                        source.ExprFunction(
                            Set_Ch, lc_last_handled_notified, (lc_arb_2,)),
                        source.ExprFunction(
                            Ch, C_channel_to_SMT_channel, (i32v('ch'),))
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
            precondition_assumption=eq(
                coerce_varkind(lc),
                coerce_varkind(lc_arb_3)
            ),
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
            ),
            postcondition=recv_postcondition(
                source.ExprFunction(MsgInfo, source.FunctionName(
                    'C_msg_info_to_SMT_msg_info'), [i64ret]),
                lc_arb_3),
            loop_invariants={}
        ),
        "libsel4cp.seL4_ReplyRecv": source.Ghost(
            precondition_assumption=eq(
                coerce_varkind(lc),
                coerce_varkind(lc_arb_4)
            ),
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
            ),
            postcondition=replyrecv_postcondition(
                source.ExprFunction(MsgInfo, source.FunctionName(
                    'C_msg_info_to_SMT_msg_info'), [i64ret]),
                lc_arb_4,
            ),
            loop_invariants={}
        ),
        "libsel4cp.handler_loop": source.Ghost(precondition=T,
                                               postcondition=T,
                                               loop_invariants={lh(handler_loop_node_name()): conjs(
                                                                     source.expr_implies(neq(charv('have_reply'), char(0)), eq(
                                                                         g('reply_tag'), source.expr_true)),
                                                                     source.expr_implies(
                                                                         eq(g('is_endpoint'), T),
                                                                         eq(neq(i64v('is_endpoint'), i64(0)),
                                                                            neq(charv('have_reply'), char(0)))
                                                                     ),
                                                                     eq(htd_assigned(), T),
                                                                     eq(mem_assigned(), T),
                                                                     eq(pms_assigned(), T),
                                                                     eq(ghost_asserts_assigned(), T),
                                                                     eq(g('have_reply'), T),
                                                                     # required for verification:
                                                                     source.expr_implies(
                                                                         conjs( eq(g('lbadge'), T), eq(i64v('lbadge'), i64(0)) ),
                                                                         conjs(
                                                                             eq(i64v('is_endpoint'), i64(0)),
                                                                             eq(g('lbadge'), T),
                                                                             eq(g('idx'), T),
                                                                             eq(htd_assigned(), T),
                                                                             eq(mem_assigned(), T),
                                                                             eq(pms_assigned(), T),
                                                                             eq(ghost_asserts_assigned(), T),
                                                                             # required for verification (loop 10 exit conds):
                                                                             eq(
                                                                                 i64v('lbadge'),
                                                                                 source.expr_shift_right(
                                                                                     source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                                     source.ExprFunction(source.type_word64, source.FunctionName("(_ zero_extend 32)"), [i32v('idx')])
                                                                                 )
                                                                             ),
                                                                             eq(
                                                                                 source.expr_shift_left(
                                                                                     i64v('lbadge'),
                                                                                     source.ExprFunction(source.type_word64, source.FunctionName("(_ zero_extend 32)"), [i32v('idx')])
                                                                                 ),
                                                                                 source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                             ),
                                                                             ule(
                                                                                 i32v('idx'),
                                                                                 i32(63)
                                                                             ),
                                                                             eq(
                                                                                 i64(0),
                                                                                 source.expr_shift_right(
                                                                                     source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                                     i64(63)
                                                                                 )
                                                                             ),
                                                                             eq(
                                                                                 i64(0),
                                                                                 source.expr_shift_right(
                                                                                     i64v('lbadge'),
                                                                                     i64(63)
                                                                                 )
                                                                             ),
                                                                             eq(
                                                                                 source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"),[
                                                                                   source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                                   source.ExprFunction(source.type_word64, lc_last_handled_notified, [lc])
                                                                                 ]),
                                                                                 source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_empty"), [])
                                                                             ),
                                                                             eq(
                                                                                 source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_union"),[
                                                                                   source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                                   source.ExprFunction(source.type_word64, lc_last_handled_notified, [lc])
                                                                                 ]),
                                                                                 source.ExprFunction(Set_Ch, NextRecvNotificationGet, [source.ExprFunction(NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])])
                                                                             ),
                                                                             eq(
                                                                                 source.ExprFunction(Maybe_Prod_Ch_MsgInfo,Prod_Ch_MsgInfo_Nothing, []),
                                                                                 source.ExprFunction(Maybe_Prod_Ch_MsgInfo,lc_unhandled_ppcall, [lc]),
                                                                             ),
                                                                             eq(
                                                                                 source.ExprFunction(Maybe_MsgInfo, source.FunctionName("handler_loop_pre_unhandled_reply"), []),
                                                                                 source.ExprFunction(Maybe_MsgInfo,lc_last_handled_reply, [lc]),
                                                                             ),
                                                                             eq(
                                                                                 source.ExprFunction(NextRecv, NR_Unknown, []),
                                                                                 source.ExprFunction(NextRecv, lc_receive_oracle, [lc]),
                                                                             ),
                                                                         )
                                                                     ),
                                                                 ),
                                                                 lh('10'): conjs(
                                                                     eq(i64v('is_endpoint'), i64(0)),
                                                                     eq(g('lbadge'), T),
                                                                     eq(g('idx'), T),
                                                                     eq(htd_assigned(), T),
                                                                     eq(mem_assigned(), T),
                                                                     eq(pms_assigned(), T),
                                                                     eq(ghost_asserts_assigned(), T),
                                                                     # required for verification:
                                                                     eq(
                                                                         i64v('lbadge'),
                                                                         source.expr_shift_right(
                                                                             source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                             source.ExprFunction(source.type_word64, source.FunctionName("(_ zero_extend 32)"), [i32v('idx')])
                                                                         )
                                                                     ),
                                                                     eq(
                                                                         source.expr_shift_left(
                                                                             i64v('lbadge'),
                                                                             source.ExprFunction(source.type_word64, source.FunctionName("(_ zero_extend 32)"), [i32v('idx')])
                                                                         ),
                                                                         source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                     ),
                                                                     ule(
                                                                         i32v('idx'),
                                                                         i32(63)
                                                                     ),
                                                                     eq(
                                                                         i64(0),
                                                                         source.expr_shift_right(
                                                                             source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                             i64(63)
                                                                         )
                                                                     ),
                                                                     eq(
                                                                         i64(0),
                                                                         source.expr_shift_right(
                                                                             i64v('lbadge'),
                                                                             i64(63)
                                                                         )
                                                                     ),
                                                                     eq(
                                                                         source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"),[
                                                                           source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                           source.ExprFunction(source.type_word64, lc_last_handled_notified, [lc])
                                                                         ]),
                                                                         source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_empty"), [])
                                                                     ),
                                                                     eq(
                                                                         source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_union"),[
                                                                           source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc]),
                                                                           source.ExprFunction(source.type_word64, lc_last_handled_notified, [lc])
                                                                         ]),
                                                                         source.ExprFunction(Set_Ch, NextRecvNotificationGet, [source.ExprFunction(NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])])
                                                                     ),
                                                                     eq(
                                                                         source.ExprFunction(Maybe_Prod_Ch_MsgInfo,Prod_Ch_MsgInfo_Nothing, []),
                                                                         source.ExprFunction(Maybe_Prod_Ch_MsgInfo,lc_unhandled_ppcall, [lc]),
                                                                     ),
                                                                     eq(
                                                                         source.ExprFunction(Maybe_MsgInfo, source.FunctionName("handler_loop_pre_unhandled_reply"), []),
                                                                         source.ExprFunction(Maybe_MsgInfo,lc_last_handled_reply, [lc]),
                                                                     ),
                                                                     eq(
                                                                         source.ExprFunction(NextRecv, NR_Unknown, []),
                                                                         source.ExprFunction(NextRecv, lc_receive_oracle, [lc]),
                                                                     ),
                                                                 )
                                                                })
    }
}

# handle loop related verification conditions
lc_progvar = source.ExprVar(source.TypeBitVec(
    PLATFORM_CONTEXT_BIT_SIZE), source.ProgVarName('GhostAssertions'))
handle_loop_pre_oracle: source.ExprT[Any] = source.ExprFunction(
    NextRecv, source.FunctionName('handler_loop_pre_receive_oracle'), [])
handle_loop_pre_oracle_ty: source.ExprT[Any] = source.ExprFunction(
    NextRecvEnum, NextRecvEnumGet, [handle_loop_pre_oracle])
handle_loop_pre_unhandled_reply: source.ExprT[Any] = source.ExprFunction(
    Maybe_MsgInfo, source.FunctionName('handler_loop_pre_unhandled_reply'), [])

recv_oracle_kernel: source.ExprT[Any] = source.ExprFunction(
    Prod_MsgInfo_SeL4_Ntfn, source.FunctionName('recv_oracle_kernel'), [])


def wf_handler_pre_unhandled_reply_with_set_ghost() -> source.ExprT[source.ProgVarName]:
    wf_condition = conjs(
        # if Nothing then all other bits are zero
        source.expr_implies(
            eq(
                source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                                    handle_loop_pre_unhandled_reply]),
                source.ExprFunction(Maybe_MsgInfoEnum,
                                    Maybe_MsgInfoEnumNothing, [])
            ),
            conjs(
                eq(
                    handle_loop_pre_unhandled_reply,
                    source.ExprNum(Maybe_MsgInfo, 0)
                ),
                eq(
                    source.ExprFunction(source.TypeBitVec(8), source.FunctionName("have_reply____Bool@v~2"), []),
                    source.ExprNum(source.type_word8, 0)
                )
            )
        ),
        # if no have_reply then no unhandled_reply either
        source.expr_implies(
            eq(
                source.ExprFunction(source.TypeBitVec(8), source.FunctionName("have_reply____Bool@v~2"), []),
                source.ExprNum(source.type_word8, 0)
            ),
            eq(
                source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                                    handle_loop_pre_unhandled_reply]),
                source.ExprFunction(Maybe_MsgInfoEnum,
                                    Maybe_MsgInfoEnumNothing, [])
            )
        )
    )

    return conjs(
        wf_condition,
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_unhandled_reply, [lc_progvar]),
            handle_loop_pre_unhandled_reply
        )
    )


# if Nothing then all other bits are zero

def wf_handler_pre_receive_oracle_with_set_ghost() -> source.ExprT[source.ProgVarName]:
    # the top two bits are valid.
    # check if the receive oracle is a valid enum

    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    valid_enum = ors(
        is_notification,
        eq(
            handle_loop_pre_oracle_ty,
            source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
        ),
    )

    valid_pre_handler_notification = source.expr_implies(
        is_notification,
        conjs(
            neq(
                source.ExprFunction(Set_Ch, NextRecvNotificationGet, [
                                    handle_loop_pre_oracle]),
                source.ExprFunction(Set_Ch, Ch_set_empty, [])
            ),
        )
    )

    # we sort of don't care about sections of the bitvector we don't access
    # as a result we can just assume its correct, even though it might not be.
    valid_ppcall = T
    valid_unknown = T
    wf_receive = conjs(
        valid_enum, valid_pre_handler_notification, valid_ppcall, valid_unknown)

    return conjs(
        wf_receive,
        eq(
            source.ExprFunction(NextRecv, lc_receive_oracle, [lc_progvar]),
            handle_loop_pre_oracle
        )
    )


def receive_oracle_relation() -> source.ExprT[source.ProgVarName]:
    # case 1: notis
    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    notification = source.ExprFunction(
        Set_Ch, NextRecvNotificationGet, [handle_loop_pre_oracle])

    badge = source.ExprFunction(SeL4_Ntfn, source.FunctionName(
        'Prod_MsgInfo_SeL4_Ntfn.snd'), [recv_oracle_kernel])


    ch_checks: list[source.ExprT[source.ProgVarName]] = []

    # eq check instead of badge_has_channel (which made dsa graph too wide)
    ch_checks = [
      eq(notification, badge),
      eq(
          i64(0),
          source.expr_shift_right(
              badge,
              i64(63)
          )
      ),
      eq(
          source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_intersection"),[
            source.ExprFunction(source.type_word64, lc_unhandled_notified, [lc_progvar]),
            source.ExprFunction(source.type_word64, lc_last_handled_notified, [lc_progvar])
          ]),
          source.ExprFunction(source.type_word64, source.FunctionName("Ch_set_empty"), [])
      ),
    ]

    # case 2: ppcalls
    is_ppcall = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumPPCall, [])
    )

    the_ppcall = source.ExprFunction(
        Prod_Ch_MsgInfo, NextRecvPPCallGet, [handle_loop_pre_oracle])

    the_ch = source.ExprFunction(
        Ch, Prod_Ch_MsgInfo_fst, [the_ppcall])

    the_msginfo = source.ExprFunction(
        MsgInfo, Prod_Ch_MsgInfo_snd, [the_ppcall])

    pp_checks = [
      eq(
          i64(0),#TODO: this is very much unsound, fix it
          i64(1)
      ),
    ]

    # reply pending
    no_reply_pending = eq(
        source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
                            handle_loop_pre_unhandled_reply]),
        source.ExprFunction(Maybe_MsgInfoEnum,
                            Maybe_MsgInfoEnumNothing, [])
    )

    have_reply_lvar = source.ExprFunction(source.TypeBitVec(8), source.FunctionName("have_reply____Bool@v~2"), [])
    rt_assigned_lvar = source.ExprFunction(source.type_bool, source.FunctionName("reply_tag___struct_seL4_MessageInfo_C@v.words_C.0@assigned~2"), [])

    no_reply_pending_kernel = conjs(
        eq(have_reply_lvar, char(0)),
        eq(rt_assigned_lvar, T)
    )

    relation = conjs(
        source.expr_implies(
            is_notification,
            conjs(*ch_checks)
        ),
        source.expr_implies(
            is_ppcall,
            conjs(*pp_checks)
        ),
        source.expr_implies(
          no_reply_pending,
          no_reply_pending_kernel
        ),
        source.expr_implies(
          no_reply_pending_kernel,
          no_reply_pending
        )
    )

    return relation

# ALERT! CONTRADICTIONS HERE WILL LEAD TO UNSOUNDNESS SINCE THIS TURNS INTO AN ASSUME NODE
# TRY TO INSERT True = False here and you will endup with ubc telling you verified the function.


def handler_loop_iter_pre() -> source.ExprT[source.ProgVarName]:

    return conjs(
        # lc_unhandled_reply lc = lc_unhandled_reply_pre
        wf_handler_pre_unhandled_reply_with_set_ghost(),

        eq(
            source.ExprFunction(Set_Ch, lc_unhandled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),
        # this cond is required, but was missing from the dec 5 version of the spec:
        eq(
            source.ExprFunction(Set_Ch, lc_last_handled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),
        
        # so is this cond: no unhandled replies at start!
        eq(
            source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumGet, [
               source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar])]),
            source.ExprFunction(Maybe_MsgInfoEnum, Maybe_MsgInfoEnumNothing, [])
        ),
        eq(
            source.ExprFunction(MsgInfo, MsgInfo_Just_1, [
               source.ExprFunction(Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar])]),
            i64(0)
        ),
        eq(
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                lc_unhandled_ppcall, [lc_progvar]),
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                Prod_Ch_MsgInfo_Nothing, [])
        ),

        # lc_receive_oracle lc = lc_receive_oracle_pre
        wf_handler_pre_receive_oracle_with_set_ghost(),
        receive_oracle_relation(),
    )


def handler_loop_iter_post() -> source.ExprT[source.ProgVarName]:

    is_notification = eq(
        handle_loop_pre_oracle_ty,
        source.ExprFunction(NextRecvEnum, NextRecvEnumNotification, [])
    )

    return conjs(
        eq(
            source.ExprFunction(
                Maybe_MsgInfo, lc_last_handled_reply, [lc_progvar]),
            handle_loop_pre_unhandled_reply
        ),
        eq(
            source.ExprFunction(Set_Ch, lc_unhandled_notified, [lc_progvar]),
            source.ExprFunction(Set_Ch, Ch_set_empty, [])
        ),
        eq(
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                lc_unhandled_ppcall, [lc_progvar]),
            source.ExprFunction(Maybe_Prod_Ch_MsgInfo,
                                Prod_Ch_MsgInfo_Nothing, [])
        ),
        eq(
            source.ExprFunction(NextRecv, lc_receive_oracle, [lc_progvar]),
            source.ExprFunction(NextRecv, NR_Unknown, [])
        ),
        source.expr_implies(
            is_notification,
            eq(
                source.ExprFunction(
                    Set_Ch, lc_last_handled_notified, [lc_progvar]),
                source.ExprFunction(Set_Ch, NextRecvNotificationGet, [
                                    handle_loop_pre_oracle])
            )
        )
    )
