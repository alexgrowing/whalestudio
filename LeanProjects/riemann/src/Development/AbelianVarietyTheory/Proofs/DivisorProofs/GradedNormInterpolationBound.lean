import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualGramInterp

open Matrix

section Block

variable {n : Type} [Fintype n] [DecidableEq n]

theorem block_mix (M P₀ Ps : Matrix n n ℂ) (l : ℂ) (hPs : Ps = (1 - l) • M + l • P₀)
    (h0 : IsUnit P₀.det) (hs : IsUnit Ps.det) :
    (Ps⁻¹ * M - 1 - l • (P₀⁻¹ * M - 1)) * (1 + (1 - l) • (P₀⁻¹ * M - 1)) =
      -(l * (1 - l)) • ((P₀⁻¹ * M - 1) * (P₀⁻¹ * M - 1)) := by
  set w := P₀⁻¹ * M - 1 with hw
  have hx : P₀⁻¹ * M = 1 + w := by rw [hw]; abel
  have e1 : M * (1 + (1 - l) • w) = Ps * (P₀⁻¹ * M) := by
    rw [hPs, hw]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv _ h0, Matrix.one_mul]
    module
  have h1 : Ps⁻¹ * M * (1 + (1 - l) • w) = 1 + w := by
    rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hs, Matrix.one_mul, hx]
  have e2 : (Ps⁻¹ * M - 1 - l • w) * (1 + (1 - l) • w) =
      Ps⁻¹ * M * (1 + (1 - l) • w) - (1 + l • w) * (1 + (1 - l) • w) := by
    rw [← Matrix.sub_mul]; congr 1; abel
  rw [e2, h1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

theorem block_lin (Y : Matrix n n ℂ) (a a₀ l : ℂ) (h : l * a₀ = a) :
    (1 + a • Y) - 1 - l • ((1 + a₀ • Y) - 1) = 0 := by
  rw [add_sub_cancel_left, add_sub_cancel_left, smul_smul, h, sub_self]

end Block

section Fin

variable {k : ℕ}

theorem mix_rel (M₀ M : Matrix (Fin k) (Fin k) ℂ) (t s₀ : ℝ) (l : ℂ) (h : l * (1 - (s₀ : ℂ)) = 1 - (t : ℂ)) :
    GradedNorm.mix t M₀ M = (1 - l) • M + l • GradedNorm.mix s₀ M₀ M := by
  have ht : (t : ℂ) = 1 - l * (1 - s₀) := by rw [h]; ring
  unfold GradedNorm.mix
  push_cast
  rw [ht]
  module

theorem mixDual_inv_mul {M₀ M : Matrix (Fin k) (Fin k) ℂ} (h₀ : M₀.PosDef) (h : M.PosDef) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (GradedNorm.mixDual t M₀ M)⁻¹ * M = 1 + ((1 : ℂ) - t) • (M₀⁻¹ * M - 1) := by
  have e : (GradedNorm.mixDual t M₀ M)⁻¹ = (GradedNorm.mix t (GlobalTheory.LieMet.dualGram M₀) (GlobalTheory.LieMet.dualGram M))ᵀ := by
    rw [← GradedNorm.dualGram_mixDual ht h₀ h, GlobalTheory.LieMet.dualGram, transpose_transpose]
  have hu : IsUnit M.det := (isUnit_iff_isUnit_det _).1 h.isUnit
  rw [e]
  simp only [GradedNorm.mix, GlobalTheory.LieMet.dualGram, transpose_add, transpose_smul, transpose_transpose, Matrix.add_mul,
    Matrix.smul_mul, nonsing_inv_mul _ hu]
  push_cast
  module

end Fin

theorem gram_interp_formula : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (g : ℕ), g = ∑ τ, m τ → ∀ (Ψ : ι → Prop) (M₀ M : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ), (∀ τ, (M₀ τ).PosDef) → (∀ τ, (M τ).PosDef) → ∀ (v : Fin g → ∀ τ, Fin (m τ) → ℂ) (G : ℝ → Matrix (Fin g) (Fin g) ℂ), (∀ s a b, G s a b = ∑ τ, HermFrame.form (if Ψ τ then GradedNorm.mix s (M₀ τ) (M τ) else GradedNorm.mixDual s (M₀ τ) (M τ))⁻¹ (v a τ) (v b τ)) → IsUnit (G 1).det → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ s₀ ∈ Set.Ico (0 : ℝ) 1, ∀ s₁ ∈ Set.Ico (0 : ℝ) 1, s₁ ≠ s₀ → ∀ (l l₁ : ℂ) (V : Matrix (Fin g) (Fin g) ℂ), l = ((1 - s) / (1 - s₀) : ℝ) → l₁ = ((1 - s₁) / (1 - s₀) : ℝ) → V = G s₀ * (G 1)⁻¹ - 1 → IsUnit (1 + (1 - l) • V).det → G s = (1 + l • V + (l * (1 - l) / (l₁ * (1 - l₁))) • ((G s₁ * (G 1)⁻¹ - 1 - l₁ • V) * (1 + (1 - l₁) • V) * (1 + (1 - l) • V)⁻¹)) * G 1 := by
  intro ι _ m g hg Ψ M₀ M h₀ h v G hG hG1 s hs s₀ hs₀ s₁ hs₁ hne l l₁ V hl hl₁ hV hT
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ, N = fun t τ =>
      (if Ψ τ then GradedNorm.mix t (M₀ τ) (M τ) else GradedNorm.mixDual t (M₀ τ) (M τ))⁻¹ := ⟨_, rfl⟩
  have hG' : ∀ t a b, G t a b = ∑ τ, HermFrame.form (N t τ) (v a τ) (v b τ) := by subst hN; exact hG
  have hNΨ : ∀ t τ, Ψ τ → N t τ = (GradedNorm.mix t (M₀ τ) (M τ))⁻¹ := fun t τ hτ => by rw [hN]; simp only [if_pos hτ]
  have hNo : ∀ t τ, ¬ Ψ τ → N t τ = (GradedNorm.mixDual t (M₀ τ) (M τ))⁻¹ := fun t τ hτ => by
    rw [hN]; simp only [if_neg hτ]
  have hMu : ∀ τ, IsUnit (M τ).det := fun τ => (isUnit_iff_isUnit_det _).1 (h τ).isUnit
  have hM₀u : ∀ τ, IsUnit (M₀ τ).det := fun τ => (isUnit_iff_isUnit_det _).1 (h₀ τ).isUnit
  have hN1 : ∀ τ, N 1 τ = (M τ)⁻¹ := fun τ => by
    by_cases hτ : Ψ τ
    · rw [hNΨ 1 τ hτ, (GradedNorm.mix_values (s := 0)).2.1]
    · rw [hNo 1 τ hτ, (GradedNorm.mixDual_values (s := 0) (hM₀u τ) (hMu τ)).2.1]

  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin g) (Σ τ, Fin (m τ)) ℂ, ∀ a p, B a p = v a p.1 p.2 :=
    ⟨of fun a p => v a p.1 p.2, fun _ _ => rfl⟩
  have hGB : ∀ t, G t = B * blockDiagonal' (N t) * Bᴴ := by
    intro t
    ext a b
    rw [hG']
    refine (HermFrame.form_blockDiagonal' (N t) (fun p => v a p.1 p.2) (fun p => v b p.1 p.2)).symm.trans ?_
    simp only [HermFrame.form, dotProduct, mulVec, mul_apply, conjTranspose_apply, hB, Finset.mul_sum, Finset.sum_mul,
      Pi.star_apply, mul_assoc]
    exact Finset.sum_comm

  obtain ⟨X, hX⟩ : ∃ X : ℝ → ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ, ∀ t τ, X t τ = N t τ * M τ :=
    ⟨fun t τ => N t τ * M τ, fun _ _ => rfl⟩
  have hXD : ∀ t, blockDiagonal' (X t) * blockDiagonal' (N 1) = blockDiagonal' (N t) := by
    intro t
    rw [← blockDiagonal'_mul]
    congr 1
    funext τ
    rw [hX, hN1, Matrix.mul_assoc, mul_nonsing_inv _ (hMu τ), Matrix.mul_one]
  have hG1u : IsUnit (G 1).det := hG1
  set C := blockDiagonal' (N 1) * Bᴴ * (G 1)⁻¹ with hC
  have hBC : B * C = 1 := by
    rw [show B * C = B * blockDiagonal' (N 1) * Bᴴ * (G 1)⁻¹ by simp only [hC, Matrix.mul_assoc], ← hGB,
      mul_nonsing_inv _ hG1u]
  have hCB : C * B = 1 := (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [Fintype.card_sigma, hg]))).1 hBC
  have hU : ∀ t, G t * (G 1)⁻¹ = B * blockDiagonal' (X t) * C := by
    intro t
    rw [hGB t, hC]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (blockDiagonal' (X t)) (blockDiagonal' (N 1)), hXD]
  have cm : ∀ P Q : Matrix (Σ τ, Fin (m τ)) (Σ τ, Fin (m τ)) ℂ, B * (P * Q) * C = (B * P * C) * (B * Q * C) := by
    intro P Q
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C B, hCB, Matrix.one_mul]
  have c1 : B * (1 : Matrix (Σ τ, Fin (m τ)) (Σ τ, Fin (m τ)) ℂ) * C = 1 := by rw [Matrix.mul_one, hBC]
  have cs : ∀ P Q : Matrix (Σ τ, Fin (m τ)) (Σ τ, Fin (m τ)) ℂ, B * (P - Q) * C = B * P * C - B * Q * C := fun P Q => by rw [Matrix.mul_sub, Matrix.sub_mul]
  have ca : ∀ P Q : Matrix (Σ τ, Fin (m τ)) (Σ τ, Fin (m τ)) ℂ, B * (P + Q) * C = B * P * C + B * Q * C := fun P Q => by rw [Matrix.mul_add, Matrix.add_mul]
  have csm : ∀ (c : ℂ) (P : Matrix (Σ τ, Fin (m τ)) (Σ τ, Fin (m τ)) ℂ), B * (c • P) * C = c • (B * P * C) := fun c P => by rw [Matrix.mul_smul, Matrix.smul_mul]

  have hs₀' : (1 - s₀ : ℝ) ≠ 0 := (sub_pos.2 hs₀.2).ne'
  have hlc : l * (1 - (s₀ : ℂ)) = 1 - (s : ℂ) := by
    rw [hl]; exact_mod_cast div_mul_cancel₀ (1 - s) hs₀'
  have hl₁c : l₁ * (1 - (s₀ : ℂ)) = 1 - (s₁ : ℂ) := by
    rw [hl₁]; exact_mod_cast div_mul_cancel₀ (1 - s₁) hs₀'
  have hl₁0 : l₁ ≠ 0 := by
    rintro rfl
    have : (1 - s₁ : ℝ) = 0 := by exact_mod_cast (by rw [← hl₁c, zero_mul] : (1 : ℂ) - s₁ = 0)
    exact (sub_pos.2 hs₁.2).ne' this
  have hl₁1 : 1 - l₁ ≠ 0 := by
    intro h1
    have e : l₁ = 1 := (sub_eq_zero.1 h1).symm
    rw [e, one_mul] at hl₁c
    exact hne (by exact_mod_cast (sub_right_inj.1 hl₁c).symm)
  have hIcc : ∀ t ∈ Set.Ico (0 : ℝ) 1, t ∈ Set.Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1, ht.2.le⟩

  have hτ : ∀ τ, (l₁ * (1 - l₁)) • ((X s τ - 1 - l • (X s₀ τ - 1)) * (1 + (1 - l) • (X s₀ τ - 1))) =
      (l * (1 - l)) • ((X s₁ τ - 1 - l₁ • (X s₀ τ - 1)) * (1 + (1 - l₁) • (X s₀ τ - 1))) := by
    intro τ
    rw [hX, hX, hX]
    by_cases hψ : Ψ τ
    · rw [hNΨ _ _ hψ, hNΨ _ _ hψ, hNΨ _ _ hψ]
      have u : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (GradedNorm.mix t (M₀ τ) (M τ)).det := fun t ht =>
        (isUnit_iff_isUnit_det _).1 (GradedNorm.mix_posDef ht (h₀ τ) (h τ)).isUnit
      rw [block_mix (M τ) _ _ l (mix_rel _ _ s s₀ l hlc) (u s₀ (hIcc s₀ hs₀)) (u s hs),
        block_mix (M τ) _ _ l₁ (mix_rel _ _ s₁ s₀ l₁ hl₁c) (u s₀ (hIcc s₀ hs₀)) (u s₁ (hIcc s₁ hs₁)), smul_smul,
        smul_smul]
      congr 1
      ring
    · rw [hNo _ _ hψ, hNo _ _ hψ, hNo _ _ hψ, mixDual_inv_mul (h₀ τ) (h τ) hs,
        mixDual_inv_mul (h₀ τ) (h τ) (hIcc s₀ hs₀), mixDual_inv_mul (h₀ τ) (h τ) (hIcc s₁ hs₁),
        block_lin _ _ _ _ hlc, block_lin _ _ _ _ hl₁c, Matrix.zero_mul, Matrix.zero_mul, smul_zero, smul_zero]
  have hPi : (l₁ * (1 - l₁)) • ((X s - 1 - l • (X s₀ - 1)) * (1 + (1 - l) • (X s₀ - 1))) =
      (l * (1 - l)) • ((X s₁ - 1 - l₁ • (X s₀ - 1)) * (1 + (1 - l₁) • (X s₀ - 1))) := by
    funext τ
    simpa only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply] using hτ τ
  have hbm : ∀ P Q : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ, blockDiagonal' (P * Q) = blockDiagonal' P * blockDiagonal' Q :=
    fun P Q => blockDiagonal'_mul P Q
  have key := congrArg (fun Z => B * blockDiagonal' Z * C) hPi
  simp only [blockDiagonal'_smul, hbm, blockDiagonal'_sub, blockDiagonal'_add, blockDiagonal'_one,
    csm, cm, cs, ca, c1, ← hU] at key
  rw [← hV] at key
  have hk : l₁ * (1 - l₁) ≠ 0 := mul_ne_zero hl₁0 hl₁1
  have e : (G s * (G 1)⁻¹ - 1 - l • V) * (1 + (1 - l) • V) =
      (l * (1 - l) / (l₁ * (1 - l₁))) • ((G s₁ * (G 1)⁻¹ - 1 - l₁ • V) * (1 + (1 - l₁) • V)) := by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hk, one_smul]
  have e2 : G s * (G 1)⁻¹ - 1 - l • V = (l * (1 - l) / (l₁ * (1 - l₁))) •
      ((G s₁ * (G 1)⁻¹ - 1 - l₁ • V) * (1 + (1 - l₁) • V) * (1 + (1 - l) • V)⁻¹) := by
    rw [← Matrix.smul_mul, ← e, Matrix.mul_assoc, mul_nonsing_inv _ hT, Matrix.mul_one]
  rw [← e2]
  calc G s = G s * (G 1)⁻¹ * G 1 := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hG1u, Matrix.mul_one]
    _ = _ := by congr 1; abel

end GlobalTheory.DualGramInterp
