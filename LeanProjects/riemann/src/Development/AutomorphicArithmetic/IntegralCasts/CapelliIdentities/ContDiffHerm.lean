import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj20.Mat :
    Nat → Nat → Type :=
    fun (k r : Nat) ↦
      Matrix
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        Complex

noncomputable def UpperTheory.Reformulated.B.Qj20.Hpk :
    (k r : Nat) →
      Matrix
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        Complex :=
    fun (k r : Nat)
        (i j :
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ↦
      @ite Complex
        (And
          (@LT.lt Nat instLTNat
            (@Fin.val
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)
            r)
          (@Eq Nat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)))
        (@instDecidableAnd
          (@LT.lt Nat instLTNat
            (@Fin.val
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)
            r)
          (@Eq Nat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k))
          ((@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i).decLt
            r)
          (instDecidableEqNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)))
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
        (@ite Complex
          (And
            (@LT.lt Nat instLTNat
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j)
              r)
            (@Eq Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  j))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)))
          (@instDecidableAnd
            (@LT.lt Nat instLTNat
              (@Fin.val
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j)
              r)
            (@Eq Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  j))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k))
            ((@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  j).decLt
              r)
            (instDecidableEqNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i)
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  j))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)))
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@ite Complex
            (And
              (@LE.le Nat instLENat r
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i))
              (And
                (@LE.le Nat instLENat
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    i)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
                (@Eq
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  i j)))
            (@instDecidableAnd
              (@LE.le Nat instLENat r
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i))
              (And
                (@LE.le Nat instLENat
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    i)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
                (@Eq
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  i j))
              (r.decLe
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i))
              (@instDecidableAnd
                (@LE.le Nat instLENat
                  (@Fin.val
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    i)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
                (@Eq
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  i j)
                ((@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      i).decLe
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i j)))
            (@ite Complex
              (@Eq Nat
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
              (instDecidableEqNat
                (@Fin.val
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  i)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) r k))
              (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
              (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
            (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))))

noncomputable def UpperTheory.Reformulated.B.Qj20.inLie :
    (k r : Nat) → UpperTheory.Reformulated.B.Qj20.Mat k r → Prop :=
    fun (k r : Nat) (X : UpperTheory.Reformulated.B.Qj20.Mat k r) ↦
      @Eq
        (Matrix
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Complex)
        (@HAdd.hAdd
          (Matrix
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Complex)
          (Matrix
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Complex)
          (Matrix
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Complex)
          (@instHAdd
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (@Matrix.add
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex Complex.instAdd))
          (@HMul.hMul
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex
              (Fin.fintype
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex.instMul Complex.instAddCommMonoid)
            (@Matrix.conjTranspose
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              X)
            (UpperTheory.Reformulated.B.Qj20.Hpk k r))
          (@HMul.hMul
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (UpperTheory.Reformulated.B.Qj20.Mat k r)
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex
              (Fin.fintype
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex.instMul Complex.instAddCommMonoid)
            (UpperTheory.Reformulated.B.Qj20.Hpk k r) X))
        (@OfNat.ofNat
          (Matrix
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Complex)
          (nat_lit 0)
          (@Zero.toOfNat0
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex)
            (@Matrix.zero
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex Complex.instZero)))

theorem UpperTheory.Reformulated.B.Qj20.aux4 :
    ∀ (n : Nat),
      @IsTopologicalRing (Matrix (Fin n) (Fin n) Complex)
        (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
        (@Matrix.nonUnitalNonAssocRing (Fin n) Complex
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))
          (Fin.fintype n)) := by
  intro n
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Qj20.RdV.{u_1} :
    {n : Nat} →
      {E : Type u_1} →
        [inst : NormedAddCommGroup E] →
          [@NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] →
            Matrix (Fin n) (Fin n) Complex → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E :=
    fun {n : Nat} {E : Type u_1} [inst : NormedAddCommGroup E]
        [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
        (X : Matrix (Fin n) (Fin n) Complex) (f : Matrix (Fin n) (Fin n) Complex → E) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @deriv Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) E
        (@NormedAddCommGroup.toAddCommGroup E inst)
        (@NormedSpace.toModule Real E Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)
          (@NormedSpace.complexToReal E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))
        (@UniformSpace.toTopologicalSpace E
          (@PseudoMetricSpace.toUniformSpace E
            (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst))))
        (fun (t : Real) ↦
          f
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              g
              (@NormedSpace.exp (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
                (UpperTheory.Reformulated.B.Qj20.aux4 n)
                (@HSMul.hSMul Complex (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
                  (@instHSMul Complex (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.smul (Fin n) (Fin n) Complex Complex (@instSMulOfMul Complex Complex.instMul)))
                  (↑t : Complex) X))))
        (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))

noncomputable def UpperTheory.Reformulated.B.Qj20.herm.{u_1} :
    {ι : Type u_1} → [Fintype ι] → Matrix ι ι Complex → (ι → Complex) → (ι → Complex) → Complex :=
    fun {ι : Type u_1} [inst : Fintype ι] (H : Matrix ι ι Complex) (v w : ι → Complex) ↦
      @dotProduct ι Complex inst Complex.instMul Complex.instAddCommMonoid
        (@Star.star (ι → Complex)
          (@Pi.instStarForall ι (fun (a : ι) ↦ Complex) fun (i : ι) ↦
            @InvolutiveStar.toStar Complex
              (@StarAddMonoid.toInvolutiveStar Complex
                (@AddCommMonoid.toAddMonoid Complex
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                (@StarRing.toStarAddMonoid Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                  Complex.instStarRing)))
          w)
        (@Matrix.mulVec ι ι Complex
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
          inst H v)

noncomputable def UpperTheory.Reformulated.B.Qj20.bvec :
    {m : Nat} → Fin m → Fin m → Complex :=
    fun {m : Nat} (i : Fin m) ↦
      @Pi.single (Fin m) (fun (a : Fin m) ↦ Complex) (fun (i : Fin m) ↦ Complex.instZero) (instDecidableEqFin m) i
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))

theorem UpperTheory.Reformulated.B.Qj20.aux8 :
    ∀ (k r : Nat) (a : Fin r),
      @LT.lt Nat instLTNat (@Fin.val r a)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
            k)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  intro k r a
  have := a.isLt
  omega

noncomputable def UpperTheory.Reformulated.B.Qj20.eI :
    (k r : Nat) →
      Fin r →
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                r)
              k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) :=
    fun (k r : Nat) (a : Fin r) ↦
      @Fin.mk
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
            k)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.val r a) (UpperTheory.Reformulated.B.Qj20.aux8 k r a)

noncomputable def UpperTheory.Reformulated.B.Qj20.Top.{u_1} :
    {n : Nat} →
      {E : Type u_1} →
        [inst : NormedAddCommGroup E] →
          [@NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] →
            (Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E) →
              Complex → Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E :=
    fun {n : Nat} {E : Type u_1} [inst : NormedAddCommGroup E]
        [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
        (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E) (u : Complex)
        (a b : Fin n) (f : Matrix (Fin n) (Fin n) Complex → E) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @HAdd.hAdd E E E
        (@instHAdd E
          (@AddCommMagma.toAdd E
            (@AddCommSemigroup.toAddCommMagma E
              (@AddCommMonoid.toAddCommSemigroup E
                (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))))))
        (@ite E (@Eq (Fin n) a b) (instDecidableEqFin n a b)
          (@HSMul.hSMul Complex E E
            (@instHSMul Complex E
              (@SMulZeroClass.toSMul Complex E
                (@AddZero.toZero E
                  (@AddZeroClass.toAddZero E
                    (@AddMonoid.toAddZeroClass E
                      (@SubNegMonoid.toAddMonoid E
                        (@AddGroup.toSubNegMonoid E
                          (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))))
                (@DistribSMul.toSMulZeroClass Complex E
                  (@AddMonoid.toAddZeroClass E
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E
                        (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))
                  (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst))))
                    (@Module.toDistribMulAction Complex E Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))
                      (@NormedSpace.toModule Complex E Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))))))
            u (f g))
          (@OfNat.ofNat E (nat_lit 0)
            (@Zero.toOfNat0 E
              (@NegZeroClass.toZero E
                (@SubNegZeroMonoid.toNegZeroClass E
                  (@SubtractionMonoid.toSubNegZeroMonoid E
                    (@SubtractionCommMonoid.toSubtractionMonoid E
                      (@AddCommGroup.toDivisionAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst)))))))))
        (Eop a b f g)

noncomputable def UpperTheory.Reformulated.B.Qj20.qminorOp.{u_1} :
    {n : Nat} →
      {E : Type u_1} →
        [inst : NormedAddCommGroup E] →
          [@NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] →
            {t : Nat} →
              (Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E) →
                (Fin t → Fin n) →
                  (Fin t → Fin n) → Complex → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E :=
    fun {n : Nat} {E : Type u_1} [inst : NormedAddCommGroup E]
        [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
        {t : Nat} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E)
        (a b : Fin t → Fin n) (u : Complex) (f : Matrix (Fin n) (Fin n) Complex → E) ↦
      ∑ σ : Equiv.Perm (Fin t),
        @HSMul.hSMul Complex (Matrix (Fin n) (Fin n) Complex → E) (Matrix (Fin n) (Fin n) Complex → E)
          (@instHSMul Complex (Matrix (Fin n) (Fin n) Complex → E)
            (@Function.hasSMul (Matrix (Fin n) (Fin n) Complex) Complex E
              (@SMulZeroClass.toSMul Complex E
                (@AddZero.toZero E
                  (@AddZeroClass.toAddZero E
                    (@AddMonoid.toAddZeroClass E
                      (@SubNegMonoid.toAddMonoid E
                        (@AddGroup.toSubNegMonoid E
                          (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))))
                (@DistribSMul.toSMulZeroClass Complex E
                  (@AddMonoid.toAddZeroClass E
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E
                        (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))
                  (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst))))
                    (@Module.toDistribMulAction Complex E Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))
                      (@NormedSpace.toModule Complex E Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1)))))))
          (@Int.cast Complex Complex.instIntCast
            (@Units.val Int Int.instMonoid
              (@DFunLike.coe
                (@MonoidHom (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (Equiv.Perm (Fin t)) (fun (x : Equiv.Perm (Fin t)) ↦ @Units Int Int.instMonoid)
                (@MonoidHom.instFunLike (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (@Equiv.Perm.sign (Fin t) (instDecidableEqFin t) (Fin.fintype t)) σ)))
          (@List.foldr ((Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E)
            (Matrix (Fin n) (Fin n) Complex → E)
            (fun (T : (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E)
                (h : Matrix (Fin n) (Fin n) Complex → E) ↦
              T h)
            f
            (@List.ofFn ((Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E) t fun (k : Fin t) ↦
              @UpperTheory.Reformulated.B.Qj20.Top n E inst inst_1 Eop
                (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) u
                  (@Nat.cast Complex Complex.instNatCast (@Fin.val t k)))
                (a
                  (@DFunLike.coe (Equiv.Perm (Fin t)) (Fin t) (fun (x : Fin t) ↦ Fin t)
                    (@EquivLike.toFunLike (Equiv.Perm (Fin t)) (Fin t) (Fin t) (@Equiv.instEquivLike (Fin t) (Fin t))) σ k))
                (b k)))

theorem UpperTheory.Reformulated.B.Qj20.aux12 :
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo := by
  exact ⟨by decide⟩

noncomputable def UpperTheory.Reformulated.B.Qj20.hpart1 :
    {n : Nat} → Matrix (Fin n) (Fin n) Complex → Matrix (Fin n) (Fin n) Complex → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (H Z : Matrix (Fin n) (Fin n) Complex) ↦
      @HSMul.hSMul Complex (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
        (@instHSMul Complex (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.smul (Fin n) (Fin n) Complex Complex (@instSMulOfMul Complex Complex.instMul)))
        (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@OfNat.ofNat Complex (nat_lit 2)
            (@instOfNatAtLeastTwo Complex (nat_lit 2) Complex.instNatCast UpperTheory.Reformulated.B.Qj20.aux12)))
        (@HSub.hSub (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@instHSub (Matrix (Fin n) (Fin n) Complex) (@Matrix.sub (Fin n) (Fin n) Complex Complex.instSub)) Z
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@Inv.inv (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.inv (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.commRing) H)
              (@Matrix.conjTranspose (Fin n) (Fin n) Complex
                (@InvolutiveStar.toStar Complex
                  (@StarAddMonoid.toInvolutiveStar Complex
                    (@AddCommMonoid.toAddMonoid Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                Z))
            H))

noncomputable def UpperTheory.Reformulated.B.Qj20.hpart2 :
    {n : Nat} → Matrix (Fin n) (Fin n) Complex → Matrix (Fin n) (Fin n) Complex → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (H Z : Matrix (Fin n) (Fin n) Complex) ↦
      @HSMul.hSMul Complex (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
        (@instHSMul Complex (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.smul (Fin n) (Fin n) Complex Complex (@instSMulOfMul Complex Complex.instMul)))
        (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
            (@OfNat.ofNat Complex (nat_lit 2)
              (@instOfNatAtLeastTwo Complex (nat_lit 2) Complex.instNatCast UpperTheory.Reformulated.B.Qj20.aux12))
            Complex.I))
        (@HAdd.hAdd (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@instHAdd (Matrix (Fin n) (Fin n) Complex) (@Matrix.add (Fin n) (Fin n) Complex Complex.instAdd)) Z
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@Inv.inv (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.inv (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.commRing) H)
              (@Matrix.conjTranspose (Fin n) (Fin n) Complex
                (@InvolutiveStar.toStar Complex
                  (@StarAddMonoid.toInvolutiveStar Complex
                    (@AddCommMonoid.toAddMonoid Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                Z))
            H))

noncomputable def UpperTheory.Reformulated.B.Qj20.EabH.{u_1} :
    {n : Nat} →
      {E : Type u_1} →
        [inst : NormedAddCommGroup E] →
          [@NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] →
            Matrix (Fin n) (Fin n) Complex →
              Fin n → Fin n → (Matrix (Fin n) (Fin n) Complex → E) → Matrix (Fin n) (Fin n) Complex → E :=
    fun {n : Nat} {E : Type u_1} [inst : NormedAddCommGroup E]
        [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
        (H : Matrix (Fin n) (Fin n) Complex) (a b : Fin n) (f : Matrix (Fin n) (Fin n) Complex → E)
        (g : Matrix (Fin n) (Fin n) Complex) ↦
      @HAdd.hAdd E E E
        (@instHAdd E
          (@AddCommMagma.toAdd E
            (@AddCommSemigroup.toAddCommMagma E
              (@AddCommMonoid.toAddCommSemigroup E
                (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))))))
        (@UpperTheory.Reformulated.B.Qj20.RdV n E inst inst_1
          (@UpperTheory.Reformulated.B.Qj20.hpart1 n H
            (@Matrix.single (Fin n) (Fin n) Complex (instDecidableEqFin n) (instDecidableEqFin n) Complex.instZero a b
              (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))))
          f g)
        (@HSMul.hSMul Complex E E
          (@instHSMul Complex E
            (@SMulZeroClass.toSMul Complex E
              (@AddZero.toZero E
                (@AddZeroClass.toAddZero E
                  (@AddMonoid.toAddZeroClass E
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E
                        (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))))
              (@DistribSMul.toSMulZeroClass Complex E
                (@AddMonoid.toAddZeroClass E
                  (@SubNegMonoid.toAddMonoid E
                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))
                (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                  (@SubNegMonoid.toAddMonoid E
                    (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst))))
                  (@Module.toDistribMulAction Complex E Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))
                    (@NormedSpace.toModule Complex E Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))))))
          Complex.I
          (@UpperTheory.Reformulated.B.Qj20.RdV n E inst inst_1
            (@UpperTheory.Reformulated.B.Qj20.hpart2 n H
              (@Matrix.single (Fin n) (Fin n) Complex (instDecidableEqFin n) (instDecidableEqFin n) Complex.instZero a b
                (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))))
            f g))

noncomputable def UpperTheory.Reformulated.B.Qj20.xR :
    (k r m : Nat) →
      @LE.le Nat instLENat m r →
        Fin m →
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) :=
    fun (k r m : Nat) (h : @LE.le Nat instLENat m r) (l : Fin m) ↦ UpperTheory.Reformulated.B.Qj20.eI k r (@Fin.castLE m r h l)

noncomputable def UpperTheory.Reformulated.B.Qj20.AAop.{u_1} :
    {E : Type u_1} →
      [inst : NormedAddCommGroup E] →
        [@NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)] →
          (k r m : Nat) →
            @LE.le Nat instLENat m r →
              Complex →
                (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Complex →
                    E) →
                  Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Complex →
                    E :=
    fun {E : Type u_1} [inst : NormedAddCommGroup E]
        [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
        (k r m : Nat) (hm : @LE.le Nat instLENat m r) (u : Complex)
        (f :
          Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Complex →
            E)
        (g :
          Matrix
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Complex) ↦
      ∑ c :
        Fin m →
          Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  r)
                k)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
        @ite E
          (@StrictMono (Fin m)
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))
            (@PartialOrder.toPreorder
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.instPartialOrder
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            c)
          (@instDecidableStrictMonoOfForallForallForallLt (Fin m)
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))
            (@PartialOrder.toPreorder
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Fin.instPartialOrder
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            c
            (@Nat.decidableForallFin m
              (fun (a : Fin m) ↦
                ∀ (b : Fin m),
                  @LT.lt (Fin m) (@Preorder.toLT (Fin m) (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))) a b →
                    @LT.lt
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Preorder.toLT
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                              k)
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@PartialOrder.toPreorder
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Fin.instPartialOrder
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (c a) (c b))
              fun (a : Fin m) ↦
              @Nat.decidableForallFin m
                (fun (b : Fin m) ↦
                  @LT.lt (Fin m) (@Preorder.toLT (Fin m) (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))) a b →
                    @LT.lt
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Preorder.toLT
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                              k)
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@PartialOrder.toPreorder
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Fin.instPartialOrder
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (c a) (c b))
                fun (a_1 : Fin m) ↦
                @forall_prop_decidable
                  (@LT.lt (Fin m) (@Preorder.toLT (Fin m) (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))) a
                    a_1)
                  (fun
                      (a_2 :
                        @LT.lt (Fin m) (@Preorder.toLT (Fin m) (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m)))
                          a a_1) ↦
                    @LT.lt
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Preorder.toLT
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                              k)
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@PartialOrder.toPreorder
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Fin.instPartialOrder
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                                k)
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (c a) (c a_1))
                  (@Fin.decLt m a a_1)
                  fun
                    (h :
                      @LT.lt (Fin m) (@Preorder.toLT (Fin m) (@PartialOrder.toPreorder (Fin m) (@Fin.instPartialOrder m))) a
                        a_1) ↦
                  (fun (a a_2 : Fin m) ↦
                      @Fin.decLt
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            k)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (c a) (c a_2))
                    a a_1))
          (@HSMul.hSMul Complex E E
            (@instHSMul Complex E
              (@SMulZeroClass.toSMul Complex E
                (@AddZero.toZero E
                  (@AddZeroClass.toAddZero E
                    (@AddMonoid.toAddZeroClass E
                      (@SubNegMonoid.toAddMonoid E
                        (@AddGroup.toSubNegMonoid E
                          (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))))
                (@DistribSMul.toSMulZeroClass Complex E
                  (@AddMonoid.toAddZeroClass E
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E
                        (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))
                  (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                    (@SubNegMonoid.toAddMonoid E
                      (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst))))
                    (@Module.toDistribMulAction Complex E Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))
                      (@NormedSpace.toModule Complex E Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))))))
            (@Matrix.det (Fin m) (instDecidableEqFin m) (Fin.fintype m) Complex Complex.commRing
              (@DFunLike.coe (Equiv (Fin m → Fin m → Complex) (Matrix (Fin m) (Fin m) Complex)) (Fin m → Fin m → Complex)
                (fun (x : Fin m → Fin m → Complex) ↦ Matrix (Fin m) (Fin m) Complex)
                (@EquivLike.toFunLike (Equiv (Fin m → Fin m → Complex) (Matrix (Fin m) (Fin m) Complex))
                  (Fin m → Fin m → Complex) (Matrix (Fin m) (Fin m) Complex)
                  (@Equiv.instEquivLike (Fin m → Fin m → Complex) (Matrix (Fin m) (Fin m) Complex)))
                (@Matrix.of (Fin m) (Fin m) Complex) fun (a l : Fin m) ↦
                @UpperTheory.Reformulated.B.Qj20.herm
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (UpperTheory.Reformulated.B.Qj20.Hpk k r)
                  (@Matrix.mulVec
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    g
                    (@UpperTheory.Reformulated.B.Qj20.bvec
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (c l)))
                  (@UpperTheory.Reformulated.B.Qj20.bvec
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        k)
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (UpperTheory.Reformulated.B.Qj20.eI k r (@Fin.castLE m r hm a)))))
            (@UpperTheory.Reformulated.B.Qj20.qminorOp
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  k)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              E inst inst_1 m
              (@UpperTheory.Reformulated.B.Qj20.EabH
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    k)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                E inst inst_1 (UpperTheory.Reformulated.B.Qj20.Hpk k r))
              (UpperTheory.Reformulated.B.Qj20.xR k r m hm) c u f g))
          (@OfNat.ofNat E (nat_lit 0)
            (@Zero.toOfNat0 E
              (@NegZeroClass.toZero E
                (@SubNegZeroMonoid.toNegZeroClass E
                  (@SubtractionMonoid.toSubNegZeroMonoid E
                    (@SubtractionCommMonoid.toSubtractionMonoid E
                      (@AddCommGroup.toDivisionAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))))))))

section helpers
namespace UpperTheory.Reformulated.B.Qj20

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem Hpk_herm (k r : ℕ) : (Hpk k r).conjTranspose = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      (s : ℕ) = if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i :=
    ⟨⟨if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i,
      by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs <;> split_ifs <;> first | omega | simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ s := fun h => hb (Fin.ext h)
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hs <;> split_ifs <;> first | omega | rfl
    rw [h0, zero_mul]
  · simp

private theorem Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_right_inv (Hpk_sq k r)

private theorem inLie_hpart1 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [inLie, hpart1, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, ← smul_add]
  simp

private theorem inLie_hpart2 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  simp only [inLie, hpart2, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, neg_smul,
    add_comm (Hpk k r * Z), neg_add_cancel]

private theorem contDiff_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  contDiff_apply_apply ℝ ℂ i j

private theorem contDiff_cst {n : ℕ} (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  contDiff_const

private theorem contDiff_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : Matrix (Fin n) (Fin n) ℂ => herm H (g.mulVec v) w) := by
  simp only [herm, dotProduct, Matrix.mulVec]
  refine ContDiff.sum fun a _ => contDiff_const.mul ?_
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact ContDiff.sum fun c _ => (contDiff_entry b c).mul contDiff_const

private theorem contDiff_det {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ → Fin m → Fin m → ℂ)
    (hA : ∀ a l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => A g a l)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (Matrix.of (A g)).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun l _ => hA _ _)

private theorem closed_sum {X E ι : Type*} [AddCommMonoid E] (P : (X → E) → Prop)
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x) (h0 : P fun _ => 0)
    (s : Finset ι) (F : ι → X → E) (hF : ∀ i, P (F i)) : P fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ (hF a) ih

private theorem closed_foldr {Y : Type*} (P : Y → Prop) (f : Y) (hf : P f) (L : List (Y → Y))
    (hL : ∀ T ∈ L, ∀ y, P y → P (T y)) : P (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact hL T (List.mem_cons_self ..) _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

end UpperTheory.Reformulated.B.Qj20
end helpers

theorem UpperTheory.Reformulated.B.Qj20.aa_closed.{u_1} :
    ∀ {k r : Nat} {E : Type u_1} [inst : NormedAddCommGroup E]
      [inst_1 : @NormedSpace Complex E Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup E inst)]
      (P : (UpperTheory.Reformulated.B.Qj20.Mat k r → E) → Prop),
      (∀ (X : UpperTheory.Reformulated.B.Qj20.Mat k r) (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E),
          UpperTheory.Reformulated.B.Qj20.inLie k r X →
            P f →
              P
                (@UpperTheory.Reformulated.B.Qj20.RdV
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                      k)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  E inst inst_1 X f)) →
        (∀ (f₁ f₂ : UpperTheory.Reformulated.B.Qj20.Mat k r → E),
            P f₁ →
              P f₂ →
                P fun (x : UpperTheory.Reformulated.B.Qj20.Mat k r) ↦
                  @HAdd.hAdd E E E
                    (@instHAdd E
                      (@AddCommMagma.toAdd E
                        (@AddCommSemigroup.toAddCommMagma E
                          (@AddCommMonoid.toAddCommSemigroup E
                            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))))))
                    (f₁ x) (f₂ x)) →
          (∀ (φ : UpperTheory.Reformulated.B.Qj20.Mat k r → Complex),
              @ContDiff Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)
                  (UpperTheory.Reformulated.B.Qj20.Mat k r)
                  (@Matrix.normedAddCommGroup
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Complex
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Complex.instNormedAddCommGroup)
                  (@Matrix.normedSpace Real
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Complex
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          k)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@NontriviallyNormedField.toNormedField Real
                      (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField))
                    (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                    (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      instInnerProductSpaceRealComplex))
                  Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  (@WithTop.some ENat (@Top.top ENat instTopENat)) φ →
                ∀ (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E),
                  P f →
                    P fun (x : UpperTheory.Reformulated.B.Qj20.Mat k r) ↦
                      @HSMul.hSMul Complex E E
                        (@instHSMul Complex E
                          (@SMulZeroClass.toSMul Complex E
                            (@AddZero.toZero E
                              (@AddZeroClass.toAddZero E
                                (@AddMonoid.toAddZeroClass E
                                  (@SubNegMonoid.toAddMonoid E
                                    (@AddGroup.toSubNegMonoid E
                                      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))))
                            (@DistribSMul.toSMulZeroClass Complex E
                              (@AddMonoid.toAddZeroClass E
                                (@SubNegMonoid.toAddMonoid E
                                  (@AddGroup.toSubNegMonoid E
                                    (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst)))))
                              (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                                (@SubNegMonoid.toAddMonoid E
                                  (@AddGroup.toSubNegMonoid E
                                    (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst))))
                                (@Module.toDistribMulAction Complex E Complex.instSemiring
                                  (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst))
                                  (@NormedSpace.toModule Complex E Complex.instNormedField
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup E inst) inst_1))))))
                        (φ x) (f x)) →
            (P fun (x : UpperTheory.Reformulated.B.Qj20.Mat k r) ↦
                @OfNat.ofNat E (nat_lit 0)
                  (@Zero.toOfNat0 E
                    (@NegZeroClass.toZero E
                      (@SubNegZeroMonoid.toNegZeroClass E
                        (@SubtractionMonoid.toSubNegZeroMonoid E
                          (@SubtractionCommMonoid.toSubtractionMonoid E
                            (@AddCommGroup.toDivisionAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst)))))))) →
              ∀ (m : Nat) (hm : @LE.le Nat instLENat m r) (u : Complex) (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E),
                P f → P (@UpperTheory.Reformulated.B.Qj20.AAop E inst inst_1 k r m hm u f) := by
  intro k r E inst inst_1 P hR hadd hmul h0 m hm u f hf
  have hc : ∀ (c : ℂ) (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E), P f → P fun x => c • f x :=
    fun c f hf => hmul (fun _ => c) (UpperTheory.Reformulated.B.Qj20.contDiff_cst c) f hf
  have hE : ∀ a b (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E), P f →
      P (UpperTheory.Reformulated.B.Qj20.EabH (UpperTheory.Reformulated.B.Qj20.Hpk k r) a b f) := fun a b f hf =>
    hadd _ _ (hR _ f (UpperTheory.Reformulated.B.Qj20.inLie_hpart1 k r _) hf)
      (hc _ _ (hR _ f (UpperTheory.Reformulated.B.Qj20.inLie_hpart2 k r _) hf))
  have hT : ∀ (v : ℂ) a b (f : UpperTheory.Reformulated.B.Qj20.Mat k r → E), P f →
      P (UpperTheory.Reformulated.B.Qj20.Top (UpperTheory.Reformulated.B.Qj20.EabH (UpperTheory.Reformulated.B.Qj20.Hpk k r)) v a b f) := by
    intro v a b f hf
    refine hadd (fun g => if a = b then v • f g else 0) _ ?_ (hE a b f hf)
    by_cases hab : a = b
    · simp only [if_pos hab]
      exact hc v f hf
    · simp only [if_neg hab]
      exact h0
  have hQ : ∀ (a b : Fin m → Fin (2 * r + k + 1)),
      P (UpperTheory.Reformulated.B.Qj20.qminorOp (UpperTheory.Reformulated.B.Qj20.EabH (UpperTheory.Reformulated.B.Qj20.Hpk k r)) a b u f) := by
    intro a b
    unfold UpperTheory.Reformulated.B.Qj20.qminorOp
    rw [Finset.sum_fn]
    refine UpperTheory.Reformulated.B.Qj20.closed_sum P hadd h0 _ _ fun σ => ?_
    refine hc _ _ (UpperTheory.Reformulated.B.Qj20.closed_foldr P f hf _ fun T hTm => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hTm
    exact hT _ _ _
  unfold UpperTheory.Reformulated.B.Qj20.AAop
  refine UpperTheory.Reformulated.B.Qj20.closed_sum P hadd h0 _ _ fun c => ?_
  by_cases hcm : StrictMono c
  · simp only [if_pos hcm]
    exact hmul _ (UpperTheory.Reformulated.B.Qj20.contDiff_det _ fun a l => UpperTheory.Reformulated.B.Qj20.contDiff_herm _ _ _) _
      (hQ _ c)
  · simp only [if_neg hcm]
    exact h0
