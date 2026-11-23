import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HermExt

open Matrix

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {m : ℕ}

def stdGram (h : HermFam K (Fin m → K)) (σ : K' →+* ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => h.form (σ.comp (algebraMap K K')) (Pi.single i 1) (Pi.single j 1)

theorem stdGram_posDef (h : HermFam K (Fin m → K)) (σ : K' →+* ℂ) : (stdGram h σ).PosDef := by
  have := h.posDef (σ.comp (algebraMap K K')) m (fun i => Pi.single i 1)
    (by
      have hb := (Pi.basisFun K (Fin m)).linearIndependent
      rwa [show ⇑(Pi.basisFun K (Fin m)) = fun i => Pi.single i 1 from funext (Pi.basisFun_apply K (Fin m))] at hb)
  exact this

def extForm (h : HermFam K (Fin m → K)) (σ : K' →+* ℂ) (x y : Fin m → K') : ℂ :=
  star (fun i => σ (x i)) ⬝ᵥ (stdGram h σ *ᵥ fun i => σ (y i))

theorem extForm_gram (h : HermFam K (Fin m → K)) (σ : K' →+* ℂ) {n : ℕ} (v : Fin n → Fin m → K') :
    (Matrix.of fun k l => extForm h σ (v k) (v l)) =
      (Matrix.of fun i k => σ (v k i))ᴴ * stdGram h σ * Matrix.of fun i k => σ (v k i) := by
  ext k l
  simp only [extForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

def extFam (h : HermFam K (Fin m → K)) : HermFam K' (Fin m → K') where
  form := extForm h
  add_right σ x y z := by
    simp only [extForm, Pi.add_apply, map_add]
    rw [show (fun i => σ (y i) + σ (z i)) = (fun i => σ (y i)) + fun i => σ (z i) from rfl,
      Matrix.mulVec_add, dotProduct_add]
  smul_right σ a x y := by
    simp only [extForm, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ a * σ (y i)) = σ a • fun i => σ (y i) from rfl, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  conj_symm σ x y := by
    have hH := (stdGram_posDef h σ).isHermitian
    simp only [extForm, dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e := hH.apply i j
    simp only [Complex.star_def] at e
    rw [e]
    ring
  posDef σ n v hv := by
    rw [extForm_gram]
    refine (stdGram_posDef h σ).conjTranspose_mul_mul_same ?_
    rw [Matrix.mulVec_injective_iff]
    letI := σ.toAlgebra
    exact linearIndependent_algebraMap_comp_iff.2 hv

theorem isBC_extFam (h : HermFam K (Fin m → K)) : IsBC h (extFam (K' := K') h) := by
  intro σ i j
  have e : ∀ j : Fin m, (fun k => σ ((Pi.single j (1 : K') : Fin m → K') k)) = Pi.single j 1 := by
    intro j; funext k; by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  show extForm h σ _ _ = _
  simp only [extForm, e]
  simp [stdGram, Matrix.mulVec_single_one, dotProduct, Pi.single_apply]

theorem exists_isBC : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (h : HermFam K (Fin m → K)), ∃ h' : HermFam K' (Fin m → K'), IsBC h h' :=
  fun _ _ _ _ _ _ _ _ h => ⟨extFam h, isBC_extFam h⟩

end GlobalTheory.HermExt
