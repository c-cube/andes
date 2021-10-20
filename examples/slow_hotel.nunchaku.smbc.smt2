
; expect: sat
; generated by nunchaku
(declare-datatypes () ((state (S1) 
                              (S2) 
                              (S3) 
                              (S4) 
                              (S5) 
                              (S6))))
(declare-datatypes () ((guest (G1) 
                              (G2))))
(declare-datatypes () ((option (None) 
                               (Some (select-Some-0 guest)))))
(declare-datatypes () ((room (R1))))
(declare-fun owns (state room) option)
(declare-datatypes () ((key (K1) 
                            (K2) 
                            (K3) 
                            (K4))))
(declare-fun currk (state room) key)
(declare-fun issued (state key) Bool)
(declare-datatypes () ((card (C1) 
                             (C2) 
                             (C3) 
                             (C4) 
                             (C5))))
(declare-fun cards (state guest card) Bool)
(declare-fun roomk (state room) key)
(declare-fun isin (state room guest) Bool)
(declare-fun safe (state room) Bool)
(declare-fun next (state state) Bool)
(assert
 (forall
    ((s1 state))
    (forall
       ((sH state))
       (= (next s1 sH)
        (or
         (and (= s1 S1) (= sH S2)) 
         (and (= s1 S2) (= sH S3)) 
         (and (= s1 S3) (= sH S4)) 
         (and (= s1 S4) (= sH S5)) 
         (and (= s1 S5) (= sH S6)))))))
(declare-fun reachH (state) Bool)
(declare-fun fst (card) key)
(declare-fun snd (card) key)
(declare-fun buggy () Bool)
(declare-fun s10 (state) state)
(declare-fun r11 (key state) room)
(declare-fun s12 (state) state)
(declare-fun sH3 (state) state)
(declare-fun K4_0 (state) key)
(declare-fun C5_0 (state) card)
(declare-fun R6 (state) room)
(declare-fun G7 (state) guest)
(declare-fun s18 (state) state)
(declare-fun sH9 (state) state)
(declare-fun G10 (state) guest)
(declare-fun C11 (state) card)
(declare-fun K12 (state) key)
(declare-fun KH13 (state) key)
(declare-fun r114 (state) room)
(declare-fun R15 (state) room)
(declare-fun rb16 (room state) room)
(declare-fun g117 (room state) guest)
(declare-fun s118 (state) state)
(declare-fun sH19 (state) state)
(declare-fun R20 (state) room)
(declare-fun G21 (state) guest)
(assert
 (forall
    ((a state))
    (=> (reachH a)
     (or
      (and
       (= a (s10 a)) 
       (= (s10 a) S1) 
       (forall ((r1 room)) (= (owns (s10 a) r1) None)) 
       (forall
          ((r1_0 room))
          (forall
             ((rH room))
             (=> (= (currk (s10 a) r1_0) (currk (s10 a) rH)) (= r1_0 rH)))) 
       (forall
          ((k key))
          (and
           (=> (issued (s10 a) k) (= (currk (s10 a) (r11 k a)) k)) 
           (=> (exists ((r1_1 room)) (= (currk (s10 a) r1_1) k))
            (issued (s10 a) k)))) 
       (forall ((g1 guest)) (forall ((c card)) (not (cards (s10 a) g1 c)))) 
       (forall ((r1_2 room)) (= (roomk (s10 a) r1_2) (currk (s10 a) r1_2))) 
       (forall
          ((r1_3 room))
          (forall ((g1_0 guest)) (not (isin (s10 a) r1_3 g1_0)))) 
       (forall ((r1_4 room)) (safe (s10 a) r1_4))) 
      (and
       (= a (sH3 a)) 
       (next (s12 a) (sH3 a)) 
       (reachH (s12 a)) 
       (not (issued (s12 a) (K4_0 a))) 
       (= (fst (C5_0 a)) (currk (s12 a) (R6 a))) 
       (= (snd (C5_0 a)) (K4_0 a)) 
       (forall
          ((r1_5 room))
          (= (owns (sH3 a) r1_5)
           (ite (= r1_5 (R6 a)) (Some (G7 a)) (owns (s12 a) r1_5)))) 
       (forall
          ((r1_6 room))
          (= (currk (sH3 a) r1_6)
           (ite (= r1_6 (R6 a)) (K4_0 a) (currk (s12 a) r1_6)))) 
       (forall
          ((k_0 key))
          (and
           (=> (issued (sH3 a) k_0)
            (or (= k_0 (K4_0 a)) (issued (s12 a) k_0))) 
           (=> (or (= k_0 (K4_0 a)) (issued (s12 a) k_0))
            (issued (sH3 a) k_0)))) 
       (forall
          ((g1_1 guest))
          (forall
             ((c_0 card))
             (and
              (=> (cards (sH3 a) g1_1 c_0)
               (or
                (and (= g1_1 (G7 a)) (= c_0 (C5_0 a))) 
                (cards (s12 a) g1_1 c_0))) 
              (=>
               (or
                (and (= g1_1 (G7 a)) (= c_0 (C5_0 a))) 
                (cards (s12 a) g1_1 c_0))
               (cards (sH3 a) g1_1 c_0))))) 
       (forall ((r1_7 room)) (= (roomk (sH3 a) r1_7) (roomk (s12 a) r1_7))) 
       (forall
          ((r1_8 room))
          (forall
             ((g1_2 guest))
             (and
              (=> (isin (sH3 a) r1_8 g1_2) (isin (s12 a) r1_8 g1_2)) 
              (=> (isin (s12 a) r1_8 g1_2) (isin (sH3 a) r1_8 g1_2))))) 
       (forall
          ((r1_9 room))
          (and
           (=> (safe (sH3 a) r1_9)
            (and (not (= r1_9 (R6 a))) (safe (s12 a) r1_9))) 
           (=> (and (not (= r1_9 (R6 a))) (safe (s12 a) r1_9))
            (safe (sH3 a) r1_9))))) 
      (and
       (= a (sH9 a)) 
       (next (s18 a) (sH9 a)) 
       (reachH (s18 a)) 
       (cards (s18 a) (G10 a) (C11 a)) 
       (= (fst (C11 a)) (K12 a)) 
       (= (snd (C11 a)) (KH13 a)) 
       (or
        (= (roomk (s18 a) (r114 a)) (K12 a)) 
        (= (roomk (s18 a) (r114 a)) (KH13 a))) 
       (forall ((ra room)) (= (owns (sH9 a) ra) (owns (s18 a) ra))) 
       (forall ((ra_0 room)) (= (currk (sH9 a) ra_0) (currk (s18 a) ra_0))) 
       (forall
          ((k_1 key))
          (and
           (=> (issued (sH9 a) k_1) (issued (s18 a) k_1)) 
           (=> (issued (s18 a) k_1) (issued (sH9 a) k_1)))) 
       (forall
          ((g1_3 guest))
          (forall
             ((c_1 card))
             (and
              (=> (cards (sH9 a) g1_3 c_1) (cards (s18 a) g1_3 c_1)) 
              (=> (cards (s18 a) g1_3 c_1) (cards (sH9 a) g1_3 c_1))))) 
       (forall
          ((ra_1 room))
          (= (roomk (sH9 a) ra_1)
           (ite (= ra_1 (R15 a)) (KH13 a) (roomk (s18 a) ra_1)))) 
       (forall
          ((ra_2 room))
          (forall
             ((g1_4 guest))
             (and
              (=> (isin (sH9 a) ra_2 g1_4)
               (or
                (and (= ra_2 (R15 a)) (= g1_4 (G10 a))) 
                (isin (s18 a) ra_2 g1_4))) 
              (=>
               (or
                (and (= ra_2 (R15 a)) (= g1_4 (G10 a))) 
                (isin (s18 a) ra_2 g1_4))
               (isin (sH9 a) ra_2 g1_4))))) 
       (forall
          ((ra_3 room))
          (and
           (=> (safe (sH9 a) ra_3)
            (ite (= ra_3 (R15 a))
              (or
               (and
                (= (owns (s18 a) (R15 a)) (Some (G10 a))) 
                (forall
                   ((rb room))
                   (forall ((g1_5 guest)) (not (isin (s18 a) rb g1_5)))) 
                (or buggy (= (KH13 a) (currk (s18 a) (R15 a))))) 
               (safe (s18 a) (R15 a)))
              (safe (s18 a) ra_3))) 
           (=>
            (ite (= ra_3 (R15 a))
              (or
               (and
                (= (owns (s18 a) (R15 a)) (Some (G10 a))) 
                (not (isin (s18 a) (rb16 ra_3 a) (g117 ra_3 a))) 
                (or buggy (= (KH13 a) (currk (s18 a) (R15 a))))) 
               (safe (s18 a) (R15 a)))
              (safe (s18 a) ra_3))
            (safe (sH9 a) ra_3))))) 
      (and
       (= a (sH19 a)) 
       (next (s118 a) (sH19 a)) 
       (reachH (s118 a)) 
       (isin (s118 a) (R20 a) (G21 a)) 
       (forall ((r1_10 room)) (= (owns (sH19 a) r1_10) (owns (s118 a) r1_10))) 
       (forall
          ((r1_11 room))
          (= (currk (sH19 a) r1_11) (currk (s118 a) r1_11))) 
       (forall
          ((k_2 key))
          (and
           (=> (issued (sH19 a) k_2) (issued (s118 a) k_2)) 
           (=> (issued (s118 a) k_2) (issued (sH19 a) k_2)))) 
       (forall
          ((g1_6 guest))
          (forall
             ((c_2 card))
             (and
              (=> (cards (sH19 a) g1_6 c_2) (cards (s118 a) g1_6 c_2)) 
              (=> (cards (s118 a) g1_6 c_2) (cards (sH19 a) g1_6 c_2))))) 
       (forall
          ((r1_12 room))
          (= (roomk (sH19 a) r1_12) (roomk (s118 a) r1_12))) 
       (forall
          ((r1_13 room))
          (forall
             ((g1_7 guest))
             (and
              (=> (isin (sH19 a) r1_13 g1_7)
               (and
                (or (not (= r1_13 (R20 a))) (not (= g1_7 (G21 a)))) 
                (isin (s118 a) r1_13 g1_7))) 
              (=>
               (and
                (or (not (= r1_13 (R20 a))) (not (= g1_7 (G21 a)))) 
                (isin (s118 a) r1_13 g1_7))
               (isin (sH19 a) r1_13 g1_7))))) 
       (forall
          ((r1_14 room))
          (and
           (=> (safe (sH19 a) r1_14) (safe (s118 a) r1_14)) 
           (=> (safe (s118 a) r1_14) (safe (sH19 a) r1_14)))))))))
(declare-fun g () guest)
(declare-fun s () state)
(declare-fun r () room)
(assert-not
 (=> (and buggy (reachH s) (safe s r) (isin s r g)) (= (owns s r) (Some g))))
(check-sat)

