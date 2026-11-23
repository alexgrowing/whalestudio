import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup

private theorem UpperTheory.Reformulated.B.Gr34.fix_pi_iff {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (∀ i, G i) M)
    (K : ∀ i, Subgroup (G i)) (m : M) :
    (∀ k ∈ Subgroup.pi Set.univ K, ρ k m = m) ↔ ∀ j, ∀ k ∈ K j, ρ (Pi.mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i _ => ?_, fun h k hk => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hk
    · simp [Pi.mulSingle_eq_of_ne hij]
  · let H : Subgroup (∀ i, G i) :=
      { carrier := {g | ρ g m = m}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : ρ a m = m) (hb : ρ b m = m) => show ρ (a * b) m = m by simp [ha, hb]
        inv_mem' := fun {a} (ha : ρ a m = m) => show ρ a⁻¹ m = m by
          conv_lhs => rw [← ha, Representation.inv_self_apply] }
    exact Subgroup.pi_mem_of_mulSingle_mem (H := H) k fun i => h i _ (hk i trivial)

theorem UpperTheory.Reformulated.B.Gr34.mem_UC :
    ∀ {L : Type} [inst : Field L] [inst_1 : @NumberField L inst] {n q : Nat} {w : Fin q → @UpperTheory.V.W.Plc L inst}
      {A M : Type} [inst_2 : CommRing A] [inst_3 : AddCommGroup M]
      [inst_4 :
        @_root_.Module A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
          (@AddCommGroup.toAddCommMonoid M inst_3)]
      (ρ :
        @Representation A (@UpperTheory.V.Hi.GV L inst inst_1 n (Fin q) w) M
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
          (@Pi.monoid (Fin q) (fun (v : Fin q) ↦ @UpperTheory.V.Hi.GLw L inst inst_1 n (w v)) fun (i : Fin q) ↦
            @Units.instMonoid
              (Matrix (Fin n) (Fin n)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                  (@NumberField.instCommRingRingOfIntegers L inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
              (@Semiring.toMonoid
                (Matrix (Fin n) (Fin n)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
                (@Matrix.semiring (Fin n)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                  (@DivisionSemiring.toSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                    (@Semifield.toDivisionSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                      (@Field.toSemifield
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))))
                  (Fin.fintype n) (instDecidableEqFin n))))
          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
      (C :
        (j : Fin q) →
          @Subgroup
            (@Units
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@ValuativeRel.ValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@ValuativeRel.valuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                (@Subring.toCommRing
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                  (@Field.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                  (@Valuation.integer
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@ValuativeRel.ValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@ValuativeRel.valuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                (@IsDiscreteValuationRing.toIsLocalRing
                  (↥(@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@Field.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.instIsDomainSubtypeMem
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@instIsDomain
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toSemifield
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                    (@UniformSpace.toTopologicalSpace
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                        (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
              (@Semiring.toMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@Field.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@IsDiscreteValuationRing.toIsLocalRing
                    (↥(@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.instIsDomainSubtypeMem
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@instIsDomain
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                      (@UniformSpace.toTopologicalSpace
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                          (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.instIsDomainSubtypeMem
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@instIsDomain
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                        (@UniformSpace.toTopologicalSpace
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                            (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@IsDiscreteValuationRing.toIsLocalRing
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.instIsDomainSubtypeMem
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@instIsDomain
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                          (@UniformSpace.toTopologicalSpace
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toCommRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.instIsDomainSubtypeMem
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@instIsDomain
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                            (@UniformSpace.toTopologicalSpace
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toCommRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.instIsDomainSubtypeMem
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@instIsDomain
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                            (@UniformSpace.toTopologicalSpace
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j))))))))))
            (@Units.instGroup
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@ValuativeRel.ValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@ValuativeRel.valuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                (@Subring.toCommRing
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                  (@Field.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                  (@Valuation.integer
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@ValuativeRel.ValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Ring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                    (@ValuativeRel.valuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                (@IsDiscreteValuationRing.toIsLocalRing
                  (↥(@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@Field.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.instIsDomainSubtypeMem
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@DivisionRing.toRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toDivisionRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@instIsDomain
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toSemifield
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                    (@UniformSpace.toTopologicalSpace
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                        (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
              (@Semiring.toMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@Subring.toCommRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@Field.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                    (@Valuation.integer
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@ValuativeRel.ValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Ring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                      (@ValuativeRel.valuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                  (@IsDiscreteValuationRing.toIsLocalRing
                    (↥(@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.instIsDomainSubtypeMem
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@instIsDomain
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                      (@UniformSpace.toTopologicalSpace
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                          (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@Subring.toCommRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Field.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                      (@Valuation.integer
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@ValuativeRel.ValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Ring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                        (@ValuativeRel.valuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.instIsDomainSubtypeMem
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@DivisionRing.toRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toDivisionRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@instIsDomain
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                        (@UniformSpace.toTopologicalSpace
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                            (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@Subring.toCommRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                        (@Valuation.integer
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@ValuativeRel.ValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Ring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                          (@ValuativeRel.valuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                      (@IsDiscreteValuationRing.toIsLocalRing
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.instIsDomainSubtypeMem
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@instIsDomain
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                          (@UniformSpace.toTopologicalSpace
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toCommRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.instIsDomainSubtypeMem
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@instIsDomain
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                            (@UniformSpace.toTopologicalSpace
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@Subring.toCommRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@Field.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Valuation.integer
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@ValuativeRel.ValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Ring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                            (@ValuativeRel.valuation
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.toCommRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@Field.toCommRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@Subring.instIsDomainSubtypeMem
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@DivisionRing.toRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toDivisionRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@instIsDomain
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                            (@Valuation.integer
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@ValuativeRel.ValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@DivisionRing.toRing
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Field.toDivisionRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Ring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@DivisionRing.toRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@Field.toDivisionRing
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers L inst)
                                        (@NumberField.instCommRingRingOfIntegers L inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))
                              (@ValuativeRel.valuation
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@DivisionRing.toRing
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toDivisionRing
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))))
                                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j)))))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                            (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                            (@UniformSpace.toTopologicalSpace
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace
                                (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)))))))))))
      (m : M),
      Iff
        (@Membership.mem M
          (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
          (@SetLike.instMembership
            (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
            M
            (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
          (@UpperTheory.V.Hi.fixd A (@UpperTheory.V.Hi.GV L inst inst_1 n (Fin q) w) M inst_2
            (@Pi.group (Fin q) (fun (v : Fin q) ↦ @UpperTheory.V.Hi.GLw L inst inst_1 n (w v)) fun (i : Fin q) ↦
              @Units.instGroup
                (Matrix (Fin n) (Fin n)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
                (@Semiring.toMonoid
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
                  (@Matrix.semiring (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))))
                    (Fin.fintype n) (instDecidableEqFin n))))
            inst_3 inst_4 ρ (@UpperTheory.V.Pa.Lev.UC L inst inst_1 q n w C))
          m)
        (∀ (j : Fin q),
          @Membership.mem M
            (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
            (@SetLike.instMembership
              (@Submodule A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)
              M
              (@Submodule.setLike A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
            (@UpperTheory.V.Hi.fixd A (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j)) M inst_2
              (@Units.instGroup
                (Matrix (Fin n) (Fin n)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                (@Semiring.toMonoid
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                  (@Matrix.semiring (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                      (@NumberField.instCommRingRingOfIntegers L inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                        (@NumberField.instCommRingRingOfIntegers L inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                          (@NumberField.instCommRingRingOfIntegers L inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                    (Fin.fintype n) (instDecidableEqFin n))))
              inst_3 inst_4
              (@MonoidHom.comp (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j)) (@UpperTheory.V.Hi.GV L inst inst_1 n (Fin q) w)
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                (@MulOneClass.toMulOne (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j))
                  (@Monoid.toMulOneClass (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j))
                    (@DivInvMonoid.toMonoid (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j))
                      (@Group.toDivInvMonoid (@UpperTheory.V.Hi.GLw L inst inst_1 n (w j))
                        (@Units.instGroup
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                      (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))))
                              (Fin.fintype n) (instDecidableEqFin n))))))))
                (@MulOneClass.toMulOne (@UpperTheory.V.Hi.GV L inst inst_1 n (Fin q) w)
                  (@Monoid.toMulOneClass (@UpperTheory.V.Hi.GV L inst inst_1 n (Fin q) w)
                    (@Pi.monoid (Fin q) (fun (v : Fin q) ↦ @UpperTheory.V.Hi.GLw L inst inst_1 n (w v)) fun (i : Fin q) ↦
                      @Units.instMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                            (@NumberField.instCommRingRingOfIntegers L inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                              (@NumberField.instCommRingRingOfIntegers L inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                (@NumberField.instCommRingRingOfIntegers L inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                  (@NumberField.instCommRingRingOfIntegers L inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                                    (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i))
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers L inst) (@NumberField.instCommRingRingOfIntegers L inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w i)))))
                            (Fin.fintype n) (instDecidableEqFin n))))))
                (@MulOneClass.toMulOne
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))))
                    M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                  (@MulZeroOneClass.toMulOneClass
                    (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                      (@RingHom.id A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    (@instMulZeroOneClassOfSemiring
                      (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                        (@RingHom.id A
                          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      (@Module.End.instSemiring A M (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_2))
                        (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))))
                ρ (@UpperTheory.V.Pa.atJ L inst inst_1 n q w j))
              (@UpperTheory.V.AlgebraTools.iwC
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                  (@NumberField.instCommRingRingOfIntegers L inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers L inst)
                  (@NumberField.instCommRingRingOfIntegers L inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                (@GlobalTheory.LocalData.complRel L inst inst_1 (w j))
                (@UniformSpace.toTopologicalSpace
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace (@NumberField.RingOfIntegers L inst)
                    (@NumberField.instCommRingRingOfIntegers L inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain L inst inst_1) L inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 L inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing L inst inst_1) (w j)))
                (@GlobalTheory.LocalData.isLocalField L inst inst_1 (w j)) n (C j)))
            m) := by
  intro L _ _ n q w A M _ _ _ ρ C m
  show m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd _ _ ↔ ∀ j, m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd _ _
  exact UpperTheory.Reformulated.B.Gr34.fix_pi_iff (G := fun j => UpperTheory.V.Hi.GLw n (w j)) ρ _ m
