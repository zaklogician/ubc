; start of pre condition
; HLIPre :: OldPlatformContext -> NewPlatformContext -> Bool
(define-fun HLIPre ((c PlatformContext) (newc PlatformContext)) Bool 
  (and
    (= (lc_unhandled_reply c) (lc_unhandled_reply newc))
    (= (lc_unhandled_notified c) (lc_unhandled_notified newc))
    (= (lc_unhandled_ppcall c) (lc_unhandled_ppcall newc))
    (not (= (lc_receive_oracle newc) NR_Unknown))
    (not (= (lc_receive_oracle newc) (NR_Notification Ch_set_empty)))
    (= (lc_receive_oracle newc) (lc_receive_oracle c))
  )
)
; HLIPost :: OldPlatformContext -> NewPlatformContext -> Bool
(define-fun HLIPost ((c PlatformContext) (newc PlatformContext)) Bool 
  (and 
    (= (lc_last_handled_reply newc) (lc_last_handled_reply c)) 
    (= (lc_unhandled_notified newc) Ch_set_empty) ; 
    (= (lc_unhandled_ppcall newc) Prod_Ch_MsgInfo_Nothing)
    (= (lc_receive_oracle newc) NR_Unknown)
    (ite
      (= (NextRecv.<> (lc_receive_oracle c)) <NR_Notification>)
      (= (lc_last_handled_notified newc) (NR_Notification.1 (lc_receive_oracle c)))
      true 
    )
  )
)
