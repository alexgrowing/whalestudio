import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot

variable {N : ℕ}

theorem mul_selM_apply {m : Type} (A : Matrix m (Fin N) ℂ) (S : Finset (Fin N)) (a : m) (b : Fin S.card) :
    (A * selM S) a b = A a (S.orderEmbOfFin rfl b) := by
  rw [Matrix.mul_apply]
  simp [selM, Matrix.of_apply]

theorem selM_conjTranspose_mul_mul (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    (selM S)ᴴ * A * selM S = A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl) := by
  ext a b
  rw [mul_selM_apply, Matrix.mul_apply]
  simp [selM, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite]

theorem det_selM (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((selM S)ᴴ * A * selM S).det = minorIJ A S S := by
  rw [selM_conjTranspose_mul_mul, minorIJ, dif_pos rfl]

theorem selM_transpose (S : Finset (Fin N)) (b : Fin S.card) :
    (selM S)ᵀ b = Pi.basisFun ℂ (Fin N) (S.orderEmbOfFin rfl b) := by
  ext a
  simp [selM, Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]

theorem linearIndependent_selM (S : Finset (Fin N)) : LinearIndependent ℂ (selM S)ᵀ := by
  have h := (Pi.basisFun ℂ (Fin N)).linearIndependent.comp _ (S.orderEmbOfFin rfl).injective
  have e : (selM S)ᵀ = (Pi.basisFun ℂ (Fin N)) ∘ (S.orderEmbOfFin rfl) := funext fun b => selM_transpose S b
  rw [e]
  exact h

theorem linearIndependent_mul_selM {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    LinearIndependent ℂ (h * selM S)ᵀ := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hi : Function.Injective h.mulVecLin := Matrix.mulVec_injective_of_isUnit hu
  have := (linearIndependent_selM S).map' h.mulVecLin (LinearMap.ker_eq_bot.2 hi)
  have e : (h * selM S)ᵀ = h.mulVecLin ∘ (selM S)ᵀ := by
    funext b
    ext a
    rfl
  rw [e]
  exact this

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (S : Finset (Fin N)) :
    0 < minorIJ G S S := by
  rw [minorIJ, dif_pos rfl]
  exact (hG.submatrix (S.orderEmbOfFin rfl).injective).det_pos

theorem log_re_mul {a b : ℂ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b).re = Real.log a.re + Real.log b.re := by
  have ha' := Complex.lt_def.1 ha
  have hb' := Complex.lt_def.1 hb
  have hi : a.im = 0 := ha'.2.symm
  rw [Complex.mul_re, hi, zero_mul, sub_zero]
  exact Real.log_mul ha'.1.ne' hb'.1.ne'

theorem gram_mul_selM (G h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((h * selM S)ᴴ * G * (h * selM S)).det = minorIJ (hᴴ * G * h) S S := by
  rw [← det_selM, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blockPot_eq_gram (N j : ℕ) (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    (∀ S : Finset (Fin N), LinearIndependent ℂ (selM S)ᵀ) ∧
    (h.det ≠ 0 → ∀ S : Finset (Fin N), LinearIndependent ℂ (h * selM S)ᵀ) ∧
    (G.PosDef → blockPot j i G h = (1 / 2) * ((if j ≤ (i : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * G * selM (wIdx N j)).det.re else 0) + (if (i : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * G * selM (omIdx N j)).det.re else 0) + (if IsProperStep N j i then Real.log ((h * selM (stepCols N j i))ᴴ * G * (h * selM (stepCols N j i))).det.re else 0))) := by
  refine ⟨linearIndependent_selM, fun hd S => linearIndependent_mul_selM hd S, fun hG => ?_⟩
  simp only [det_selM, gram_mul_selM, blockPot, detFac]
  have hW := minor_pos hG (wIdx N j)
  have hO := minor_pos hG (omIdx N j)
  split_ifs <;>
    simp only [one_mul, mul_one, Complex.one_re, Real.log_one, log_re_mul hW hO] <;> ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot
