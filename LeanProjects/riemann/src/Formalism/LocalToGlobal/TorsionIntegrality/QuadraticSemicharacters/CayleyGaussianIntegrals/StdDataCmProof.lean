import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H.CmData

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)

variable {n : Type} [Fintype n] [DecidableEq n]

def embA (a : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun w => if w.1 = a then x w.2 else 0

theorem slice_embA (a a' : Fin 4) (x : n → ℂ) : slice a' (embA a x) = if a' = a then x else 0 := by
  ext i
  by_cases h : a' = a <;> simp [slice, embA, h]

theorem embA_mem (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) {x : n → ℂ} (hx : x ∈ Λ) : embA a x ∈ pow4 Λ := by
  intro a'
  rw [slice_embA]
  split_ifs
  · exact hx
  · exact Λ.zero_mem

theorem isSelfDual_matH_blk4_pow4 (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hsd : IsSelfDual (matH h) Λ) :
    IsSelfDual (matH (blk4 h)) (pow4 Λ) := by
  ext x
  constructor
  · intro hx a
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (embA a y) (embA_mem Λ a hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [altE, matrixForm_fourfoldBlock, slice_embA]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · intro hx y hy
    have : ∀ a, ∃ m : ℤ, altE (matH h) (slice a x) (slice a y) = (m : ℝ) := fun a => by
      have h1 : slice a x ∈ dualLat (matH h) Λ := by rw [hsd]; exact hx a
      exact h1 _ (hy a)
    choose m hm using this
    refine ⟨∑ a, m a, ?_⟩
    simp only [altE] at hm
    simp only [altE, matrixForm_fourfoldBlock, Complex.im_sum, hm]
    push_cast
    rfl

theorem selfDual_img {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V)
    (H' : Sesq W) (g : V ≃ₗ[ℂ] W) (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (Λ : AddSubgroup V)
    (hsd : IsSelfDual H Λ) : IsSelfDual H' (imgLat (g : V →ₗ[ℂ] W) Λ) := by
  ext x
  constructor
  · intro hx
    refine ⟨g.symm x, ?_, by simp⟩
    show g.symm x ∈ Λ
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g y) ⟨y, hy, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg (g.symm x) y
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [altE, this]
  · rintro ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    have h1 : x' ∈ dualLat H Λ := by rw [hsd]; exact hx'
    obtain ⟨m, hm⟩ := h1 y' hy'
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg x' y'
    simp only [altE]
    exact congrArg Complex.im this

theorem odd_b (a : ℕ) (b c : ℤ) (d : ℕ) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d) (h8 : d % 8 = 7) : Odd b := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | hb
  · exfalso
    subst hk
    have h5 : 4 * ((a : ℤ) * c) = 4 * (k * k) + d := by rw [← mul_assoc, h4]; ring
    generalize (a : ℤ) * c = s at h5
    generalize k * k = t at h5
    omega
  · exact hb

theorem stdData_cm (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (h4 : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hodd : Odd a) (h8 : d % 8 = 7) (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hg : IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ)
    (i1 : relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0) :
    StdData (cmL a b d ha hd lam hlam) (lam * a) h Λ (alphaQ (Real.sqrt d / 2) (matH h))
      (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g where
  per := (cmL a b d ha hd lam hlam).ω₁_mem_lattice
  half := (cmL a b d ha hd lam hlam).ω₁_div_two_notMem_lattice
  isom := hg
  alpha0 := by simp [alphaQ, qOf]
  betaStd := fun x hx => CmStdCharScale_proof a b c d ha hd lam hlam h4 hodd h8 _ x hx
  betaSemi := by
    have hsd' := selfDual_img _ _ g hg _ (isSelfDual_matH_blk4_pow4 h Λ hsd)
    refine (quadMultiplierSemicharacter _ _ (standardFormBasic _ _).2.1 b d (odd_b a b c d h4 h8) _ (le_of_eq hsd'.symm) ?_).2.2
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  betaAlpha := by
    intro x
    rw [← quadMultiplierRules.2 n h]
    exact quadMultiplierRules.1 _ _ _ _ _ hg _ x
  selfDual := selfDual_img _ _ g hg _ (isSelfDual_matH_blk4_pow4 h Λ hsd)
  idx₁ := i1
  idx₂ := i2

end Formalism.L2.Th1.H.CmData

namespace Formalism.L2.Th1.H

theorem StdDataCm_proof : StdDataCm := by
  intro a b c d ha hd lam hlam h4 hodd h8 n _ _ h Λ g hg hsd hst i1 i2
  exact CmData.stdData_cm a b c d ha hd lam hlam h4 hodd h8 h Λ g hg hsd hst i1 i2

end Formalism.L2.Th1.H
