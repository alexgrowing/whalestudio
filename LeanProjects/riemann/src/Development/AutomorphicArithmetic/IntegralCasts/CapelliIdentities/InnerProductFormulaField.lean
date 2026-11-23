import Mathlib

noncomputable def UpperTheory.Reformulated.B.InnerProductFormulaField.GlRel.{u_2, u_5} :
    {R : Type u_2} → [DecidableEq R] → {A : Type u_5} → [Ring A] → (R → R → A) → Prop :=
    fun {R : Type u_2} [inst : DecidableEq R] {A : Type u_5} [inst_1 : Ring A] (T : R → R → A) ↦
      ∀ (a b c d : R),
        @Eq A
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T a b) (T c d))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T c d) (T a b)))
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@ite A (@Eq R b c) (inst b c) (T a d)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1))))))
            (@ite A (@Eq R d a) (inst d a) (T c b)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1)))))))

theorem UpperTheory.Reformulated.B.InnerProductFormulaField.aux2 :
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo := by
  exact ⟨le_refl _⟩

noncomputable def UpperTheory.Reformulated.B.InnerProductFormulaField.CasimirValue :
    Prop :=
    ∀ (k M : Type) [inst : CommRing k] [inst_1 : AddCommGroup M]
      [inst_2 :
        @_root_.Module k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
          (@AddCommGroup.toAddCommMonoid M inst_1)]
      (r : Nat)
      (T :
        Fin r →
          Fin r →
            @Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2),
      @UpperTheory.Reformulated.B.InnerProductFormulaField.GlRel (Fin r) (instDecidableEqFin r)
          (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
          (@Module.End.instRing k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)) inst_1 inst_2) T →
        ∀ (v : M) (κ : Fin r → k),
          (∀ (b b' : Fin r),
              @LT.lt (Fin r) (@instLTFin r) b b' →
                @Eq M
                  (@DFunLike.coe
                    (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M (fun (x : M) ↦ M)
                    (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                    (T b b') v)
                  (@OfNat.ofNat M (nat_lit 0)
                    (@Zero.toOfNat0 M
                      (@NegZeroClass.toZero M
                        (@SubNegZeroMonoid.toNegZeroClass M
                          (@SubtractionMonoid.toSubNegZeroMonoid M
                            (@SubtractionCommMonoid.toSubtractionMonoid M
                              (@AddCommGroup.toDivisionAddCommMonoid M inst_1)))))))) →
            (∀ (b : Fin r),
                @Eq M
                  (@DFunLike.coe
                    (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M (fun (x : M) ↦ M)
                    (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                    (T b b) v)
                  (@HSMul.hSMul k M M
                    (@instHSMul k M
                      (@SMulZeroClass.toSMul k M
                        (@AddZero.toZero M
                          (@AddZeroClass.toAddZero M
                            (@AddMonoid.toAddZeroClass M
                              (@SubNegMonoid.toAddMonoid M
                                (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))))
                        (@DistribSMul.toSMulZeroClass k M
                          (@AddMonoid.toAddZeroClass M
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                          (@DistribMulAction.toDistribSMul k M
                            (@Semiring.toMonoid k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1)))
                            (@Module.toDistribMulAction k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                    (κ b) v)) →
              @Eq M
                (@DFunLike.coe
                  (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  M (fun (x : M) ↦ M)
                  (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                    (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)) (@AddCommGroup.toAddCommMonoid M inst_1)
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                    (@RingHom.id k
                      (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                  (∑ b : Fin r,
                    ∑ b' : Fin r,
                      @HMul.hMul
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@instHMul
                          (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                          (@Module.End.instMul k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                        (T b b') (T b' b))
                  v)
                (@HSMul.hSMul k M M
                  (@instHSMul k M
                    (@SMulZeroClass.toSMul k M
                      (@AddZero.toZero M
                        (@AddZeroClass.toAddZero M
                          (@AddMonoid.toAddZeroClass M
                            (@SubNegMonoid.toAddMonoid M
                              (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))))
                      (@DistribSMul.toSMulZeroClass k M
                        (@AddMonoid.toAddZeroClass M
                          (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                        (@DistribMulAction.toDistribSMul k M
                          (@Semiring.toMonoid k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))
                          (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1)))
                          (@Module.toDistribMulAction k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                  (∑ b : Fin r,
                    @HMul.hMul k k k
                      (@instHMul k
                        (@Distrib.toMul k
                          (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                      (κ b)
                      (@HSub.hSub k k k
                        (@instHSub k
                          (@SubNegMonoid.toSub k
                            (@AddGroup.toSubNegMonoid k
                              (@AddGroupWithOne.toAddGroup k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))))
                        (@HSub.hSub k k k
                          (@instHSub k
                            (@SubNegMonoid.toSub k
                              (@AddGroup.toSubNegMonoid k
                                (@AddGroupWithOne.toAddGroup k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))))
                          (@HAdd.hAdd k k k
                            (@instHAdd k
                              (@Distrib.toAdd k
                                (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                            (κ b)
                            (@Nat.cast k
                              (@AddMonoidWithOne.toNatCast k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                              r))
                          (@OfNat.ofNat k (nat_lit 1)
                            (@One.toOfNat1 k
                              (@AddMonoidWithOne.toOne k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst)))))))
                        (@HMul.hMul k k k
                          (@instHMul k
                            (@Distrib.toMul k
                              (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                          (@OfNat.ofNat k (nat_lit 2)
                            (@instOfNatAtLeastTwo k (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                              UpperTheory.Reformulated.B.InnerProductFormulaField.aux2))
                          (@Nat.cast k
                            (@AddMonoidWithOne.toNatCast k
                              (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                            (@Fin.val r b)))))
                  v)
