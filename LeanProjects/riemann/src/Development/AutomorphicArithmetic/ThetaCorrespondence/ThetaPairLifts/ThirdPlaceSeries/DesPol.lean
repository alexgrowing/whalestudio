import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun.PolBound
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun.PolBound
open Formalism.BasicNotions Formalism.MainNotions NumberField
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun
open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound
theorem desPol_alt : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith
end GlobalTheory.BigTop.Fun
end
