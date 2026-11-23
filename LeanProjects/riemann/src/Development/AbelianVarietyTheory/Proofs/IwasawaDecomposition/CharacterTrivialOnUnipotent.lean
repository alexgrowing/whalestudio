import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SkewEqSumRankOneIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumRankOneIntegralRescalingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnIntegralTransvectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnSumTransvectionsStatement

namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem char_eq_one_of_sq_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  intro E _ _ _ N X hE φ γ hγ
  set A : Matrix (Fin N) (Fin N) E := ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) with hA
  set n : Matrix (Fin N) (Fin N) E := A - 1 with hn
  have h2 : n * n = 0 := by rw [← pow_two]; exact hγ
  have hiso : IsIsom X.Gm A := fun x y => (X.Γ_stab _ γ.2).1 x y
  have hsk : IsSkew X.Gm n := isSkew_sub_one X.Gm hiso h2
  set W : Submodule E (Fin N → E) := LinearMap.range (Matrix.mulVecLin n) with hW
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, herm X.Gm u v = 0 := by
    rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
    exact herm_mulVec_mulVec_eq_zero X.Gm hsk h2 x y
  have hκ : cc X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc_mul, cc_neg, X.ξ0_im, cc_two]
  have hκ0 : X.κ0 ≠ 0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  obtain ⟨d, ξ, t, hξW, ht, hnd⟩ := GlobalTheory.T.skew_eq_sum_rank_one_isotropic E N X.Gm X.κ0 X.Gm_herm X.Gm_det hκ hκ0 W hWiso n hsk
    (fun y => ⟨y, rfl⟩)
  obtain ⟨k, ξ', s, hk, hξ'Λ, hξ'a, hs, hsint, hsum⟩ := GlobalTheory.T.sum_rank_one_integral_rescaling E N X d ξ t ht
  have horth : ∀ i j, herm X.Gm (ξ' i) (ξ' j) = 0 := by
    intro i j
    obtain ⟨a, ha⟩ := hξ'a i; obtain ⟨b, hb⟩ := hξ'a j
    rw [ha, hb, herm_smul_left, herm_smul_right, hWiso _ (hξW i) _ (hξW j)]; ring
  have hkill : ∀ j, ∃ γ' : X.Γ, ((γ' : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ' j) (X.m * s j * X.κ0) ∧ φ γ' = 1 := by
    intro j
    obtain ⟨γ', hγ'Γ, hγ'⟩ := X.transv (ξ' j) (hξ'Λ j) (horth j j) (s j) (hs j) (hsint j)
    exact ⟨⟨γ', hγ'Γ⟩, hγ', GlobalTheory.T.character_trivial_on_integral_transvections E N X hE φ (ξ' j) (s j) (hξ'Λ j) (horth j j) (hs j) (hsint j) ⟨γ', hγ'Γ⟩ hγ'⟩
  obtain ⟨γ', hγ'eq, hφγ'⟩ := GlobalTheory.T.character_trivial_on_sum_transvections E N X φ d ξ' (fun j => X.m * s j * X.κ0) horth hkill
  have hpow : γ ^ k = γ' := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hγ'eq, ← hsum, ← hnd]
    have : (γ : GL (Fin N) E).val = 1 + n := by rw [hn]; abel
    rw [this, one_add_pow_of_sq_eq_zero h2]
  have hφ : φ γ ^ k = 1 := by rw [← map_pow, hpow, hφγ']
  have : k • Multiplicative.toAdd (φ γ) = 0 := by
    have := congrArg Multiplicative.toAdd hφ
    rwa [toAdd_pow, toAdd_one] at this
  have h0 := (smul_eq_zero.1 this).resolve_left hk.ne'
  exact Multiplicative.toAdd.injective (by simpa using h0)
end GlobalTheory.UnipKill
