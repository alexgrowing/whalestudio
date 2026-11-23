import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular

noncomputable section

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

def IntAt (w : HeightOneSpectrum (𝓞 K)) {κ : Type} (M : Matrix ι κ K) : Prop := ∀ i j, w.valuation K (M i j) ≤ 1

def IsAdelic (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Prop :=
  (∀ w, (A w).det ≠ 0) ∧ {w | ¬ (IntAt w (A w) ∧ IntAt w (A w)⁻¹)}.Finite

def locLat (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Submodule (𝓞 K) (ι → K) where
  carrier := {x | ∀ (w : HeightOneSpectrum (𝓞 K)) (i : ι), w.valuation K ((A w *ᵥ x) i) ≤ 1}
  zero_mem' := fun w i => by simp
  add_mem' := fun {x y} hx hy w i => by
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx w i) (hy w i))
  smul_mem' := fun a x hx w i => by
    have h : a • x = (a : K) • x := by
      funext j
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one a) (hx w i)

def matNorm (Y : (K →+* ℂ) → Matrix ι ι ℂ) (σ : K →+* ℂ) (x : ι → K) : ℝ :=
  Real.sqrt (∑ i, ‖(Y σ *ᵥ fun j => σ (x j)) i‖ ^ 2)

def detDeg (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ) : ℝ :=
  GlobalTheory.FlatLine.lineDeg (fun σ => ‖(Y σ).det‖) (fun w => (vAdd w (A w).det : ℝ))

theorem isAdelic_one : IsAdelic (fun _ : HeightOneSpectrum (𝓞 K) => (1 : Matrix ι ι K)) := by
  refine ⟨fun _ => by simp, ?_⟩
  have h : ∀ w : HeightOneSpectrum (𝓞 K), IntAt w (1 : Matrix ι ι K) := fun w i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp [h]

end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

abbrev TIdx (la : ∀ t, Fin (N t) → ℕ) : Type := ∀ t, Idx (la t)

def tval (la : ∀ t, Fin (N t) → ℕ) {S : Type} [CommRing S] (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) : S :=
  ∑ I : TIdx la, x I * ∏ t, evalAt (y t) (map (Int.castRingHom S) (intVec (la t) (I t)))

def rhoMat (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g : Matrix (Fin n) (Fin n) K) : Matrix (Idx la) (Idx la) K :=
  LinearMap.toMatrix (basis la K) (basis la K) (rho la K gᵀ)

def kron {J : T → Type} {R : Type} [CommRing R] (M : ∀ t, Matrix (J t) (J t) R) : Matrix (∀ t, J t) (∀ t, J t) R :=
  Matrix.of fun I I' => ∏ t, M t (I t) (I' t)

def onMat (la : Fin n → ℕ) : Matrix (Idx la) (Idx la) ℂ :=
  Matrix.of fun i j => (onBasis la).repr (toSpace la (basis la ℂ j)) i

def fibA (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (a : K) (B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    Matrix (TIdx la) (TIdx la) K := a • kron fun t => rhoMat (la t) (B t)

def fibY (la : ∀ t, Fin (N t) → ℕ) (s : ℝ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) : Matrix (TIdx la) (TIdx la) ℂ :=
  (s : ℂ) • kron fun t => onMat (la t) * rhoMat (la t) (X t)

example (la : ∀ t, Fin (N t) → ℕ) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℚ) : tval la 0 y = 0 := by simp [tval]

end Tensor

end GlobalTheory.DefPt

end
