(declare-fun handler_loop_pre_unhandled_reply () Maybe_MsgInfo)
(declare-fun handler_loop_pre_receive_oracle () NextRecv)

(declare-fun oracle_rel_arb_ch () Ch)
(declare-fun recv_oracle_kernel () Prod_MsgInfo_SeL4_Ntfn)
(define-fun badge_has_channel ((badge SeL4_Ntfn) (ch Ch)) Bool 
  (= 
    ((_ extract ch ch) badge)
    (_bv1 1)
  )
)
