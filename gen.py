from collections.abc import Sequence
import enum
import math
from typing import Iterable, NamedTuple

from hypothesis import control
from hypothesis.strategies._internal.strategies import Ex
from smt import CmdDefineFun, Identifier

from source import ExprType, TypeBitVec

EMIT_TESTS = True


class ExternType(NamedTuple):
    name: str
    bit_size: int
    # num_elements: int

    # @property
    # def bit_size(self):
    #     return math.ceil(math.log2(self.num_elements))


def gen_set_type(ext_type: ExternType, over_arrays: bool = False) -> ExternType:

    set_type = ExternType(f'{ext_type.name}_set', 2 ** ext_type.bit_size)
    singleton = f'{ext_type.name}_set_singleton'
    empty = f'{ext_type.name}_set_empty'
    intersection = f'{ext_type.name}_set_intersection'
    union = f'{ext_type.name}_set_union'
    has = f'{ext_type.name}_set_has'

    print(f'; Set {ext_type.name}')
    if over_arrays:
        print(f'(define-sort {set_type.name} () (Array {ext_type.name} Bool))')
        print(f'()')
        raise NotImplementedError

    else:
        print(
            f'(define-sort {set_type.name} () (_ BitVec {set_type.bit_size}))')

        # singleton containing the element 'A', with bitwise representation
        # corresponding to the natural number 'n', is straight zero, except for
        # the bit 2 ** n, which is set to 1.

        print(
            f'(define-fun {empty} () {set_type.name} (_ bv0 {set_type.bit_size}))')
        print(f'(define-fun {singleton} ((x {ext_type.name})) {set_type.name} (bvshl (_ bv1 {set_type.bit_size}) ((_ zero_extend {set_type.bit_size - ext_type.bit_size}) x)))')
        print(
            f'(define-fun {intersection} ((s1 {set_type.name}) (s2 {set_type.name})) {set_type.name} (bvand s1 s2))')
        print(
            f'(define-fun {union} ((s1 {set_type.name}) (s2 {set_type.name})) {set_type.name} (bvor s1 s2))')
        print(
            f'(define-fun {has} ((s {set_type.name}) (x {ext_type.name})) Bool (bvult (_ bv0 {set_type.bit_size}) (bvand s ({singleton} x))))')

        # complement = f'{ext_type.name}_set_complement_UNSAFE'  # can put invalid elements into a set
        # print(f'(define-fun {complement} ((s {set_type.name})) {set_type.name} (bvnot s))')  # NOT SAFE

        # convenience functions
        add = f'{ext_type.name}_set_add'
        remove = f'{ext_type.name}_set_remove'
        print(
            f'(define-fun {add} ((s {set_type.name}) (x {ext_type.name})) {set_type.name} ({union} s ({singleton} x)))')
        print(
            f'(define-fun {remove} ((s {set_type.name}) (x {ext_type.name})) {set_type.name} ({intersection} s ({singleton} x)))')

    print()
    if not EMIT_TESTS:
        return set_type

    print(f'(push)')
    print(f'    (declare-fun s1 () {set_type.name})')
    print(f'    (declare-fun s2 () {set_type.name})')
    print(f'    (declare-fun x () {ext_type.name})')
    print(f'    (declare-fun y () {ext_type.name})')

    # x in A u B = x in A or x in B
    print(f'    (push)')
    print(
        f'        (assert (not (= ({has} ({union} s1 s2) x) (or ({has} s1 x) ({has} s2 x)))))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')
    # x in A n B = x in A /\ x in B
    print(f'    (push)')
    print(
        f'        (assert (not (= ({has} ({intersection} s1 s2) x) (and ({has} s1 x) ({has} s2 x)))))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')
    # x in singl(y) = (x = y)
    print(f'    (push)')
    print(f'        (assert (not (= ({has} ({singleton} x) y) (= x y))))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')
    # x in empty = false
    print(f'    (push)')
    print(f'        (assert (not (not ({has} {empty} x))))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')
    # x in A = (A & {x}) != empty
    print(f'    (push)')
    print(
        f'        (assert (not (= ({has} s1 x) (distinct {empty} ({intersection} s1 ({singleton} x))))))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')

    print(f'(pop)')
    print()

    return set_type


def gen_prod_type(fst: ExternType, snd: ExternType) -> ExternType:
    prod = ExternType(f'Prod_{fst.name}_{snd.name}',
                      fst.bit_size + snd.bit_size)

    # (define-sort MsgInfo () (_ BitVec 80))
    # (define-fun mi_label ((mi MsgInfo)) (_ BitVec 64) ((_ extract 79 16) mi))
    # (define-fun mi_count ((mi MsgInfo)) (_ BitVec 16) ((_ extract 15 0) mi))

    # (define-fun mi_label= ((mi MsgInfo) (label (_ BitVec 64))) MsgInfo (concat label (mi_count mi)))
    # (define-fun mi_count= ((mi MsgInfo) (count (_ BitVec 16))) MsgInfo (concat (mi_label mi) count))
    print(f'; type {prod.name} = ({fst.name}, {snd.name})')
    print(f'(define-sort {prod.name} () (_ BitVec {prod.bit_size}))')
    print(define_fun(prod.name,
                     (f'(fst {fst.name})', f'(snd {snd.name})'), prod.name, concat(('fst', 'snd'))))
    print(
        f'(define-fun {prod.name}.fst ((p {prod.name})) {fst.name} ((_ extract {prod.bit_size - 1} {snd.bit_size}) p))')
    print(
        f'(define-fun {prod.name}.snd ((p {prod.name})) {snd.name} ((_ extract {snd.bit_size - 1} 0) p))')
    print(
        f'(define-fun {prod.name}.fst= ((p {prod.name}) (x {fst.name})) {prod.name} (concat x ({prod.name}.snd p)))')
    print(
        f'(define-fun {prod.name}.snd= ((p {prod.name}) (x {snd.name})) {prod.name} (concat ({prod.name}.fst p) x))')

    print()
    if not EMIT_TESTS:
        return prod

    print(f'(push)  ; testing {prod.name}')
    print(f'    (declare-fun p1 () {prod.name})')
    print(f'    (declare-fun p2 () {prod.name})')
    print(f'    (declare-fun p3 () {prod.name})')
    print(f'    (declare-fun arb.fst () {fst.name})')
    print(f'    (declare-fun arb.snd () {snd.name})')
    print()
    print(f'    (push)')
    print(f'        (assert (= p2 ({prod.name}.snd= p1 arb.snd)))')
    print(f'        (assert (= p3 ({prod.name}.fst= p2 arb.fst)))')
    print()
    print(f'        (assert (not (and')
    print(f'            (= ({prod.name}.fst p3) arb.fst)')
    print(f'            (= ({prod.name}.snd p3) arb.snd)')
    print(f'        )))')
    print(f'        (echo "should be unsat")')
    print(f'        (check-sat)')
    print(f'    (pop)')
    print(f'    (push)')
    print(f'        (echo "should be unsat")')
    print(f'        ' + assert_(not_(eq('true',
                                        eq(call(
                                            prod.name + '.fst', (call(prod.name, ('arb.fst', 'arb.snd')), )), 'arb.fst'),
                                        eq(call(
                                            prod.name + '.snd', (call(prod.name, ('arb.fst', 'arb.snd')), )), 'arb.snd'),
                                        ))))
    print(f'        (check-sat)')
    print(f'    (pop)')
    print(f'(pop)')
    print()

    return prod


def concat(xs: Sequence[str]) -> str:
    if len(xs) == 0:
        raise ValueError
    elif len(xs) == 1:
        return xs[0]
    else:
        return f'(concat {xs[0]} {concat(xs[1:])})'


def extract(bv: str, high: int, low: int) -> str:
    """ high and low are both included """
    return f'((_ extract {high} {low}) {bv})'


def gen_composite_type(name: str, constructor: str, fields: dict[str, ExternType]) -> ExternType:

    # older versions of python don't guarantee dict ordering
    ordering = tuple(fields.keys())

    comp = ExternType(name, sum(t.bit_size for t in fields.values()))

    print(f'; data {name} = {constructor}')
    print(f';   {{ {ordering[0]} :: {fields[ordering[0]].name}')
    for field in ordering[1:]:
        print(f';   , {field} :: {fields[field].name}')
    print(f';   }}')

    print(f'(define-sort {name} () (_ BitVec {comp.bit_size}))')

    args = []
    parts = []
    for i, field in enumerate(ordering):
        arg_name = chr(ord('a') + i)
        arg_type = fields[field].name
        args.append(f'({arg_name} {arg_type})')
        parts.append(arg_name)
    print(define_fun(constructor, args, name, concat(parts)))

    # print(f'; type {name}')
    top = comp.bit_size - 1
    for field in ordering:
        field_typ = fields[field]
        print(
            f'(define-fun {field} ((c {name})) {field_typ.name} {extract("c", top, top - field_typ.bit_size + 1)})')

        parts = []
        if field != ordering[0]:  # top field doesn't need to extract the fields above it
            parts.append(extract('c', comp.bit_size - 1, top + 1))
        parts.append('v')
        # bottom field doesn't need to extract the fields below it
        if field != ordering[-1]:
            parts.append(extract('c', top - field_typ.bit_size, 0))
        print(
            f'(define-fun {field}= ((c {name}) (v {field_typ.name})) {name} {concat(parts)})')

        top -= field_typ.bit_size

    print()
    if not EMIT_TESTS:
        return comp

    print(f'; test {name}')
    print(f'(push)')
    for i in range(0, len(ordering)+1):
        print(f'    (declare-fun c{i} () {name})')

    args = []
    for i, field in enumerate(ordering):
        print(f'    (declare-fun f{i} () {fields[field].name})')
        args.append(f'f{i}')

    print()
    for i, field in enumerate(ordering):
        print(f'    (assert (= c{i+1} ({field}= c{i} f{i})))')

    print()
    # (true = x = y = z) is the same as (x and y and z)
    print('    (push)')
    print('        (assert (not (= true')
    for i, field in enumerate(ordering):
        print(f'            (= ({field} c{len(fields)}) f{i})')
    print('        )))')
    print('        (echo "should be unsat")')
    print('        (check-sat)')
    print('    (pop)')
    print('    (push)')
    print('        ' +
          assert_(not_(eq(f'c{len(ordering)}', call(constructor, args)))))
    print('        (echo "should be unsat")')
    print('        (check-sat)')
    print('    (pop)')
    print(f'(pop)')
    print()

    return comp


def gen_maybe_type(a: ExternType) -> ExternType:
    return gen_nonrec_data_type('Maybe_' + a.name, {
        a.name + '_Nothing': (),
        a.name + '_Just': (a, ),
    })


def distinct(args: Iterable[str]) -> str:
    return f'(distinct {" ".join(args)})'


def assert_(expr: str) -> str:
    return f'(assert {expr})'


def define_fun(name: str, args: Sequence[str], ret: str, term: str) -> str:
    return f'(define-fun {name} ({" ".join(args)}) {ret} {term})'


def declare_fun(name: str, args: Sequence[str], ret: str) -> str:
    return f'(declare-fun {name} ({" ".join(args)}) {ret})'


def define_sort(name: str, val: str) -> str:
    return f'(define-sort {name} () {val})'


def eq(*args: str) -> str:
    return '(= ' + ' '.join(args) + ')'


def call(func: str, args: Sequence[str]) -> str:
    if len(args) == 0:
        return func
    return f'({func} {" ".join(args)})'


def not_(t: str) -> str:
    return f'(not {t})'


def gen_nonrec_data_type(data_type_name: str, constructors: dict[str, Sequence[ExternType]]) -> ExternType:
    # size is the size of the largest constructor
    # data X = A T1 T2 | B T3 T4 T5 | C
    # size(X) = max(size(T1) + size(T2), size(T3) + size(T4) + size(T5), size(<no args>))
    constructor_sort_bitsize = math.ceil(math.log2(len(constructors)))

    data = ExternType(data_type_name, constructor_sort_bitsize + max(*
                                                                     (sum(arg.bit_size for arg in args) for args in constructors.values())))

    ordering = list(constructors.keys())

    print(define_sort(data_type_name, f'(_ BitVec {data.bit_size})'))

    constructor_sort_name = f'{data_type_name}<>'
    print(define_sort(constructor_sort_name,
                      f'(_ BitVec {constructor_sort_bitsize})'))

    constructor_names = tuple(f'<{cons}>' for cons in ordering)
    for constructor_name in constructor_names:
        print(declare_fun(constructor_name, (), constructor_sort_name))

    print(assert_(distinct(f"<{constructor}>" for constructor in ordering)))

    # accessor for the constructor
    print(define_fun(
        f'{data_type_name}.<>',
        (f'(v {data_type_name})', ),
        constructor_sort_name,
        extract('v', data.bit_size - 1, data.bit_size - constructor_sort_bitsize)))

    for i, constructor in enumerate(ordering):
        # for each constructor, we have a function like this
        # (define-fun [constructor] ((a arg1) (b arg2) (c arg3)) (concat [constructor_id] a b c [padding zeros]))
        #
        #     data Maybe a = Just a | Nothing
        #     x :: Maybe Ch
        #
        # This part would generate
        #
        #     (define-fun Just (c Ch) (concat <Just> c))
        #     (define-fun Nothing () (concat <Nothing> (_ bv0 [size of ch in bits])))
        #     (define-fun Just.1 ((m Maybe)) Ch (_ extract t b) m)

        constructor_name = constructor_names[i]
        args = []
        parts = [constructor_name]
        bits_left = data.bit_size - constructor_sort_bitsize

        for j, arg in enumerate(constructors[constructor]):
            arg_name = chr(ord('a') + j)
            arg_type = arg.name
            args.append(f'({arg_name} {arg_type})')
            parts.append(arg_name)

            # accessor for this argument
            hi = bits_left - 1
            lo = bits_left - arg.bit_size
            print(define_fun(
                f'{constructor}.{j+1}', (f'(v {data_type_name})', ), arg_type, extract('v', hi, lo)))

            bits_left -= arg.bit_size

        # pad the rest with zeros
        if bits_left > 0:
            parts.append(f'(_ bv0 {bits_left})')

        ret_type = data_type_name
        body = concat(parts)

        # the constructor function (like Just or Nothing)
        print(define_fun(constructor, args, ret_type, body))

    if not EMIT_TESTS:
        return data

    # no point emiting tests for Pd and Ch, they are huge
    if data_type_name in ('PD', 'Ch'):
        return data

    print()
    print('; testing')
    for constructor in ordering:
        print(f'(push) ; test constructor {constructor}')
        print(f'    ' + declare_fun('d', (), data.name, ))

        args1: list[str] = []
        for i, arg1 in enumerate(constructors[constructor]):
            args1.append(f'arg1_{i+1}')
            print(f'    ' + declare_fun(f'arg1_{i+1}', (), arg1.name))

        print(f'    ' + assert_(eq('d', call(constructor, args1))))
        for i in range(len(constructors[constructor])):
            print(f'    (echo "should be sat")')
            print(f'    (check-sat)')
            print(f'    (push)')
            print(
                f'        ' + assert_(not_(eq(call(f'{constructor}.{i+1}', 'd'), f'arg1_{i+1}'))))
            print(f'        (echo "should be unsat")')
            print(f'        (check-sat)')
            print(f'    (pop)')

        print(f'    (echo "should be sat")')
        print(f'    (check-sat)')
        print(f'    (push)')
        print(f'        ' +
              assert_(not_(eq(call(f'{data.name}.<>', 'd'), f'<{constructor}>'))))
        print(f'        (echo "should be unsat")')
        print(f'        (check-sat)')
        print(f'    (pop)')

        # make sure that A a1 a2 a3 != B b1 b2  forall (A, B) if A != B
        for constructor2 in ordering:
            if constructor2 == constructor:
                continue
            print(f'    (echo "should be sat")')
            print(f'    (check-sat)')
            print(f'    (push)')
            args2: list[str] = []
            for i, arg2 in enumerate(constructors[constructor2]):
                args2.append(f'arg2_{i+1}')
                print(f'        ' + declare_fun(f'arg2_{i+1}', (), arg2.name))

            print(
                f'        ' + assert_(eq(call(constructor2, args2), call(constructor, args1))))
            print(f'        (echo "should be unsat")')
            print(f'        (check-sat)')
            print(f'    (pop)')
        print(f'(pop)')

    return data


print('(set-logic QF_ABV)')
print('(set-option :produce-models true)')
print()

# Ch = ExternType(name='Ch', bit_size=6)


# Test = gen_nonrec_data_type('Test', {
#     'All': (PD, Ch, Word64, Word16),
#     'Some': (Word64, Ch),
#     'Empty': ()
# })

# exit(0)

PD = gen_nonrec_data_type('PD', {f'PD{i:02}': () for i in range(62 + 1)})
Ch = gen_nonrec_data_type('Ch', {f'Ch{i:02}': () for i in range(62 + 1)})
Word64 = ExternType(name='Word64', bit_size=64)
Word16 = ExternType(name='Word16', bit_size=16)
print('(define-sort Word64 () (_ BitVec 64))')
print('(define-sort Word16 () (_ BitVec 16))')
print()

Set_Ch = gen_set_type(Ch)

# data MsgInfo = MI
#   { mi_label :: Word64
#   , mi_count :: Word16
#   } deriving (Eq, Show)
MsgInfo = gen_composite_type('MsgInfo', 'MI', {
    'label': Word64,
    'count': Word16
})
Prod_Ch_MsgInfo = gen_prod_type(Ch, MsgInfo)

# data NextRecv
#   = NR_Notification (Set Ch)
#   | NR_PPCall (Ch, MsgInfo)
#   | NR_Unknown
NextRecv = gen_nonrec_data_type('NextRecv', {
    'Notification': (Set_Ch, ),
    'PPCall': (Prod_Ch_MsgInfo, ),
    'Unknown': ()
})
Maybe_MsgInfo = gen_maybe_type(MsgInfo)
Maybe_Prod_Ch_MsgInfo = gen_maybe_type(Prod_Ch_MsgInfo)

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
pc = gen_composite_type('PlatformContext', 'LC', {
    'lc_running_pd': PD,
    'lc_receive_oracle': NextRecv,  # TODO
    'lc_unhandled_notified': Set_Ch,
    'lc_last_handled_notified': Set_Ch,
    'lc_unhandled_ppcall': Maybe_Prod_Ch_MsgInfo,
    'lc_unhandled_reply': Maybe_MsgInfo,
    'lc_last_handled_reply': Maybe_MsgInfo
})

exit(0)


def get_channels() -> None:
    constructors = []
    for i in range(63):
        print(f'(define-fun Ch_constructor_Ch{i} () Ch = (_ bv{i} 8))')
        constructors.append(f'Ch_constructor_Ch{i}')

    print(f'(assert (distinct {" ".join(constructors)}))')

    exit(0)


get_channels()
