import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

set_option synthInstance.maxHeartbeats 200000

theorem idV_incA_mul {D : D7} (c : D.host.E) (𝔞 : FI D) (v : Pl D) {y : AE D} (hy : y ∈ idV 𝔞 v) :
    incA D c * y ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (FractionalIdeal.spanSingleton _ c * 𝔞) v).comap (AddMonoidHom.mulLeft (incA D c)) := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, h₁, h₂, c * a,
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ c) ha, ?_⟩
    show incA D c * _ = _
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  exact hle hy

theorem idV_le_idAt {D : D7} (𝔞 : FI D) (v : Pl D) : idV 𝔞 v ≤ (idAt D (· = v)).toAddSubgroup := by
  rw [idV, AddSubgroup.closure_le]
  rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
  simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, idAt, Submodule.mem_inf, Submodule.mem_iInf,
    RingHom.mem_ker]
  refine ⟨?_, fun w => ?_⟩
  · change (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _)) ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = 0
    rw [Algebra.TensorProduct.map_tmul]
    change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E a) = 0
    exact TensorProduct.zero_tmul _ _
  · have e : FinPl.compAt D w.1 ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] a := rfl
    rw [e, h₂ w.1 w.2]
    exact TensorProduct.zero_tmul _ _

theorem idV_spanSingleton_mul_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s,
    s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 x hx s
  constructor
  · intro hs
    refine ⟨?_, idV_le_idAt _ v hs⟩
    have h := idV_incA_mul x⁻¹ _ v hs
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at h
  · rintro ⟨h, -⟩
    have h' := idV_incA_mul x 𝔞 v h
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at h'

end GlobalTheory.SeeSaw
