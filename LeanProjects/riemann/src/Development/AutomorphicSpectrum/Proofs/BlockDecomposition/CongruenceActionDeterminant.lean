import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise Kronecker

namespace GlobalTheory.CompanionTheory.ConeLin

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_add (v w : Fin n × Fin n → ℝ) : hOf (v + w) = hOf v + hOf w := by
  simp only [hOf, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem hOf_smul (c : ℝ) (v : Fin n × Fin n → ℝ) : hOf (c • v) = (c : ℂ) • hOf v := by
  simp only [hOf, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem hOf_single (q : Fin n × Fin n) : hOf (Pi.single q (1 : ℝ)) = hb q := by
  classical
  simp [hOf, Pi.single_apply, ite_smul]

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v)ᴴ = hOf v := by
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem re_trace (P : Mat n) (hP : Pᴴ = P) (p : Fin n × Fin n) :
    (((P * hb p).trace).re : ℂ) = (P * hb p).trace := by
  apply Complex.conj_eq_iff_re.1
  have h1 : star (P * hb p).trace = (P * hb p).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
      Matrix.trace_mul_comm]
  exact h1

theorem hOf_re (P : Mat n) (hP : Pᴴ = P) : hOf (fun p => ((P * hb p).trace).re) = P := by
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, re_trace P hP]

theorem conj_herm (g P : Mat n) (hP : Pᴴ = P) : (g * P * gᴴ)ᴴ = g * P * gᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

def realMap (g : Mat n) : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun v p := ((g * hOf v * gᴴ * hb p).trace).re
  map_add' v w := by
    funext p
    simp [hOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c v := by
    funext p
    simp [hOf_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

def cplxMap (g : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := g * X * gᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxMap_apply (g X : Mat n) : cplxMap g X = g * X * gᴴ := rfl

theorem hOf_realMap (g : Mat n) (v : Fin n × Fin n → ℝ) : hOf (realMap g v) = g * hOf v * gᴴ :=
  hOf_re _ (conj_herm g _ (hOf_herm v))

theorem det_realMap (g : Mat n) : ((LinearMap.det (realMap g) : ℝ) : ℂ) = LinearMap.det (cplxMap g) := by
  rw [← LinearMap.det_toMatrix' (realMap g), ← GlobalTheory.CompanionTheory.TopClass.det_of_trace (cplxMap g),
    ← Matrix.det_transpose (Matrix.of _)]
  have h : ((LinearMap.toMatrix' (realMap g)).det : ℂ) =
      Complex.ofRealHom (LinearMap.toMatrix' (realMap g)).det := rfl
  rw [h, RingHom.map_det]
  congr 1
  ext p q
  have hh : (g * hb q * gᴴ)ᴴ = g * hb q * gᴴ := conj_herm g _ (GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose q)
  have := re_trace _ hh p
  simpa [LinearMap.toMatrix'_apply, realMap, hOf_single, cplxMap_apply, Pi.single_apply] using this

theorem det_cplxMap (g : Mat n) : LinearMap.det (cplxMap g) = (g.det * star g.det) ^ n := by
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n)) (cplxMap g) =
      g ⊗ₖ g.map star := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hr : ∀ X : Mat n, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr X (i, j) = X i j := by
      intro X
      simp [Matrix.stdBasis]
    rw [LinearMap.toMatrix_apply, hr]
    simp [cplxMap_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)), h, Matrix.det_kronecker]
  have h2 : (g.map star).det = star g.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    rfl
  rw [h2, Fintype.card_fin, mul_pow]

theorem cone_lin (n : ℕ) (g : Mat n) (_hg : g.det ≠ 0) :
    ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  refine ⟨realMap g, hOf_realMap g, ?_⟩
  apply Complex.ofReal_injective
  rw [det_realMap, det_cplxMap]
  have : g.det * star g.det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' g.det
  rw [this, pow_mul]
  simp

end GlobalTheory.CompanionTheory.ConeLin
