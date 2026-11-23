import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.DualComm

variable {n : ℕ}

theorem sum_single_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y = c • Δ a b := by
  have hx : ∀ x y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y =
      if y = b then (if x = a then c • Δ a b else 0) else 0 := by
    intro x y
    by_cases h1 : x = a
    · by_cases h2 : y = b
      · subst h1
        subst h2
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h1, h2, Ne.symm h2]
    · simp [Matrix.single_apply, h1, Ne.symm h1]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem eq_zero_of_skew {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ x, ∑ y, X x y • Δ x y = 0) (a b : Fin n) : Δ a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
    ext i j
    simp [Matrix.single_apply]
    split_ifs <;> ring)
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single_smul, one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · exact h2

theorem dualT_comp_rho (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (ξ ∘L E.ρ k) = dualT E T ξ ∘L E.ρ k := by
  ext v
  have h := congrArg (fun f : E.V →L[ℂ] E.V => f v) (hT k)
  change T (E.ρ k v) = E.ρ k (T v) at h
  simp [dualT, h]

theorem dualT_sum (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • G a b (dualT E T ξ) := by
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro t
    have hc : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hs : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hX, smul_neg]
      simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp ((t : ℂ) • X), hmem t⟩
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have h1 := hG.2 X γ hX hγ ξ
  have h2 := hG.2 X γ hX hγ (dualT E T ξ)
  have h3 : HasDerivAt (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹))
      (dualT E T (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    ((dualT E T).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hfun : (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹)) =
      fun t : ℝ => dualT E T ξ ∘L E.ρ (γ t)⁻¹ := by
    funext t
    exact dualT_comp_rho E T hT (γ t)⁻¹ ξ
  rw [hfun] at h3
  exact h3.unique h2

theorem dualT_G : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
      ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  intro n E T hT G hG a b ξ
  have h := eq_zero_of_skew (fun a b => dualT E T (G a b ξ) - G a b (dualT E T ξ)) ?_ a b
  · exact sub_eq_zero.mp h
  · intro X hX
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← dualT_sum E T hT G hG X hX ξ]
    simp only [map_sum, map_smul]

end GlobalTheory.CompanionTheory.RealCountG.DualComm
