import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairConeChars

theorem condLE_mono {F : Type} [Field F] [NumberField F] {v : Pl F} {e m : ℕ} (hem : e ≤ m)
    {χ : (Fv F v)ˣ →* ℂˣ} (h : GlobalTheory.SplitFlip.CondLE (unifAt v) e χ) : GlobalTheory.SplitFlip.CondLE (unifAt v) m χ := by
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have h1 : ValuativeRel.valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) ≤ 1 := hϖ.mem
  intro x hx
  refine h x ⟨hx.1, hx.2.trans ?_⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' h1 hem

theorem nu_cond_at_ram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hvT
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  have hα := hT.chars.heckeα.1
  have hβ := hT.chars.heckeβ.1
  have hν : Continuous X.ν := (show Continuous fun x => X.α x / X.β x from hα.div' hβ)
  have hne : {c | GlobalTheory.SplitFlip.CondLE (unifAt v.1) c (chrW X.ν (B.τ v))}.Nonempty :=
    GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.ν hν (B.τ v))
  have hmem : GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) := Nat.sInf_mem hne
  obtain ⟨eα, heα⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.α hα (B.τ v))
  obtain ⟨eβ, heβ⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.β hβ (B.τ v))
  have hram : ¬ UnrAt X.ν (splitPrime (B.τ v)) :=
    hT.chars.ram _ (by rw [splitPrime_under]; exact hvT)
  obtain ⟨x₀, hx₀, hx₀', hνx₀⟩ := GlobalTheory.StepFacNe.chrW_ram X.ν (B.τ v) hram
  have hx₀v : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) = 1 := by
    have h1 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀
    have h2 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀'
    have h3 : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) *
        ValuativeRel.valuation (Fv F v.1) ((x₀⁻¹ : (Fv F v.1)ˣ) : Fv F v.1) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero (Fv F v.1)) = _ := h3.symm
      _ ≤ _ := mul_le_of_le_one_right' h2
  have hc1 : 1 ≤ condExp (chrW X.ν (B.τ v)) := by
    by_contra h
    have h0 : condExp (chrW X.ν (B.τ v)) = 0 := by omega
    have hm := hmem
    rw [h0] at hm
    refine hνx₀ (hm x₀ ⟨hx₀v, ?_⟩)
    rw [pow_zero, Units.val_one, map_one]
    exact ((ValuativeRel.valuation (Fv F v.1)).map_sub _ _).trans (by simp [hx₀v])
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, locChar, Chars.ν]
  refine ⟨hmem, hc1, hdiv, ⟨max eα eβ, condLE_mono (le_max_left _ _) heα, condLE_mono (le_max_right _ _) heβ⟩,
    fun x => ?_, fun x => ?_⟩
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.α (B.τ v) x
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.β (B.τ v) x

end GlobalTheory.StdPairConeChars
