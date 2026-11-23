import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem detects_restrictNormal_inf : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l))
    (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ),
    (∀ i, x i ∈ Set.range (algebraMap L (Om l))) →
    (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) →
    (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') →
    Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ r N N' I ι x a hx hN hN'
  classical
  intro σ₀ hσ₀ hσ₀B

  let lift : (L ≃ₐ[ℚ_[l]] L) → GQ l := fun s =>
    if h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s then h.choose else 1
  have hlift : ∀ s ∈ N.map (AlgEquiv.restrictNormalHom L),
      lift s ∈ N ∧ AlgEquiv.restrictNormalHom L (lift s) = s := by
    intro s hs
    have h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s := Subgroup.mem_map.mp hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hτN, hτ⟩ := hlift σ₀ hσ₀.1
  have hτN' : lift σ₀ ∉ N' := by
    intro h
    exact hσ₀B ⟨Subgroup.mem_map.mpr ⟨lift σ₀, h, hτ⟩, hσ₀.2⟩
  have hex : ∃ i, ¬ (l : ℤ) ^ r ∣ a i (lift σ₀) := by
    by_contra hc
    push_neg at hc
    exact hτN' (hN' _ hτN hc)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x', hx'⟩ := hx i
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlL : (l : L) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hnorm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
    rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  refine ⟨x', fun s => a i (lift s), ?_, hi⟩
  intro s hs
  obtain ⟨hσN, hσ⟩ := hlift s hs.1
  have key : algebraMap L (Om l) (s x') = lift s (x i) := by
    rw [← hx']
    conv_lhs => rw [← hσ]
    exact AlgEquiv.restrictNormal_commutes (lift s) L x'
  refine ⟨(s x' - x' - (a i (lift s) : L)) / (l : L) ^ r, ?_, ?_⟩
  · refine ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).1).mpr ?_
    rw [map_div₀, map_sub, map_sub, map_intCast, map_pow, map_natCast, key, hx', norm_div, norm_pow, hnorm_l]
    rw [div_le_one (by positivity)]
    exact hN i _ hσN
  · rw [mul_div_cancel₀ _ hlL]
    ring

end GlobalTheory.PMon.Ram
