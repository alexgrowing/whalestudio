import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSplit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def ballInd (l : ℤ) : F → ℂ := (valBall F (-l) : Set F).indicator fun _ => 1

def phiT (χ : AddChar F Circle) (l : ℤ) (y : F × F) : ℂ :=
  (χ y.1 : ℂ) * (χ y.2 : ℂ) * ballInd l y.1 * ballInd l y.2

def hz : GL (Fin 2) F :=
  ⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

open Ad3 Ad3.K

section Alg
variable {F : Type} [Field F]

theorem norm_pair (x : F × F) : Algebra.norm F x = x.1 * x.2 := by
  have : Algebra.lmul F (F × F) x = LinearMap.prodMap (Algebra.lmul F F x.1) (Algebra.lmul F F x.2) := by
    ext <;> simp
  rw [Algebra.norm_apply, this, LinearMap.det_prodMap]
  simp [← Algebra.norm_apply]

theorem norm_unit_pair (u : Fˣ) : Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) = 1 := by
  rw [norm_pair]; simp
end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nsg_pair {a : F} (ha : a ≠ 0) : GL2LocalData.nsg (F × F) a = 1 := by
  unfold GL2LocalData.nsg
  rw [if_pos]
  refine ⟨⟨(a, 1), (a⁻¹, 1), by ext <;> simp [ha], by ext <;> simp [ha]⟩, ?_⟩
  rw [norm_pair]; simp

end GlobalTheory.CompanionTheory.WeilSplit
