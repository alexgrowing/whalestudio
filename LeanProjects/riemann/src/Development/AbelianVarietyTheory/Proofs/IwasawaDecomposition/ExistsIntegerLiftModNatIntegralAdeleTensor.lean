import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftModG

theorem exists_lift_mod_g : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  intro D X s hs
  have hg : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  set I : Ideal (𝓞 X.B.I.E) := Ideal.span {((X.B.g : ℕ) : 𝓞 X.B.I.E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  obtain ⟨q, hq⟩ := cmpS_surj (F := X.B.I.F) I hI0 (Ideal.Quotient.mk _ ⟨s, hs⟩)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : Ideal.Quotient.mk (idS X.B.I.F I) (oToS X.B.I.F X.B.I.E a) = Ideal.Quotient.mk _ ⟨s, hs⟩ := hq
  rw [Ideal.Quotient.eq] at h1
  have h2 : (⟨s, hs⟩ - oToS X.B.I.F X.B.I.E a) ∈ Ideal.span {oToS X.B.I.F X.B.I.E ((X.B.g : ℕ) : 𝓞 X.B.I.E)} := by
    have := (Ideal.neg_mem_iff _).2 h1
    rw [neg_sub] at this
    simpa [idS, hI, Ideal.map_span] using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨RingOfIntegers.mapRingEquiv X.ιE a, t, t.2, ?_⟩
  have e1 : X.ιE.symm ((RingOfIntegers.mapRingEquiv X.ιE a : 𝓞 D.host.E) : D.host.E) = (a : X.B.I.E) := by
    rw [RingOfIntegers.mapRingEquiv_apply]; exact X.ιE.symm_apply_apply _
  rw [e1]
  have := congrArg (fun y : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E => (y : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ht
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, map_natCast, Subring.coe_natCast] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory.Mem.LiftModG
