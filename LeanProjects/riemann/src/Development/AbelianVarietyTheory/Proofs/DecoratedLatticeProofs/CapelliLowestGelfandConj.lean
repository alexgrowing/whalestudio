import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliLowest

end GlobalTheory.CapelliLowest

namespace GlobalTheory.CapelliLowest

theorem single_comm {N : ℕ} (a b c d : Fin N) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h2), h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h1), h1]
  · simp [Matrix.single_mul_single_of_ne (h := h1), Matrix.single_mul_single_of_ne (h := h2), h1, h2]

theorem lie_of_glRel {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Q X * Q Y - Q Y * Q X = Q (X * Y - Y * X) := by
  refine Matrix.induction_on' X ?_ ?_ ?_
  · simp
  · intro p q hp hq
    have e : (p + q) * Y - Y * (p + q) = (p * Y - Y * p) + (q * Y - Y * q) := by noncomm_ring
    rw [e, map_add, map_add, ← hp, ← hq]
    noncomm_ring
  · intro i j x
    refine Matrix.induction_on' Y ?_ ?_ ?_
    · simp
    · intro p q hp hq
      have e : Matrix.single i j x * (p + q) - (p + q) * Matrix.single i j x =
          (Matrix.single i j x * p - p * Matrix.single i j x) + (Matrix.single i j x * q - q * Matrix.single i j x) := by
        noncomm_ring
      rw [e, map_add, map_add, ← hp, ← hq]
      noncomm_ring
    · intro k l y
      have hx : Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hy : Matrix.single k l y = y • Matrix.single k l (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have e : x • Matrix.single i j (1 : ℂ) * (y • Matrix.single k l 1) - y • Matrix.single k l (1 : ℂ) * (x • Matrix.single i j 1)
          = (x * y) • (Matrix.single i j (1 : ℂ) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1) := by
        simp only [smul_mul_smul_comm, mul_comm y x, smul_sub]
      rw [hx, hy, e, single_comm, map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x,
        ← smul_sub, h i j k l]
      split_ifs <;> simp

theorem glRel_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) :
    Formalism.REAL.GlRel (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) := by
  have HG : (g⁻¹).1 * g.1 = 1 := g.inv_mul
  have key : ∀ X Y : Matrix (Fin N) (Fin N) ℂ, (g.1 * X * (g⁻¹).1) * (g.1 * Y * (g⁻¹).1) = g.1 * (X * Y) * (g⁻¹).1 := by
    intro X Y
    rw [show g.1 * X * (g⁻¹).1 * (g.1 * Y * (g⁻¹).1) = g.1 * X * ((g⁻¹).1 * g.1) * Y * (g⁻¹).1 by simp only [mul_assoc],
      HG, mul_one]
    simp only [mul_assoc]
  intro a b c d
  simp only
  rw [lie_of_glRel Q h, key, key, ← sub_mul, ← mul_sub, single_comm]
  split_ifs <;> simp [mul_sub, sub_mul]

theorem gelfA_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) :
    GlobalTheory.SmoothForms.gelfA (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) =
      GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1)) := by
  have hGH : g.1 * (g⁻¹).1 = 1 := g.mul_inv
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  have hE' : (fun a b => Q (g.1 * Matrix.single a b 1 * (g⁻¹).1)) =
      fun a b => ∑ c, ∑ d, ((g.1)ᵀ a c * ((g⁻¹).1)ᵀ d b) • Q (Matrix.single c d 1) := by
    funext a b
    simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (g.1 * _ * (g⁻¹).1)]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  rw [hE', GlobalTheory.RegSch.GChart.trace_pow_conj _ (g.1)ᵀ ((g⁻¹).1)ᵀ
    (by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one])]

end GlobalTheory.CapelliLowest
