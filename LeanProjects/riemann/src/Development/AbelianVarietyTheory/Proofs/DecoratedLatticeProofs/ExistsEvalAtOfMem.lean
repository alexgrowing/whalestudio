import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
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

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

section Transport

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}

theorem qdet_map (f : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet (fun a b => f (E a b)) u = f (Formalism.REAL.qdet E u) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, apply_ite f, map_zero]

end Transport

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

def lieOf {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin N → Fin N → A) (hE : Formalism.REAL.GlRel E) :
    Matrix (Fin N) (Fin N) ℂ →ₗ⁅ℂ⁆ A where
  toFun x := ∑ a, ∑ b, x a b • E a b
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]
  map_lie' {x y} := by

    have swap4 : ∀ f : Fin N → Fin N → Fin N → Fin N → A,
        ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := fun f => by
      calc _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have hXY : (∑ a, ∑ b, x a b • E a b) * (∑ c, ∑ d, y c d • E c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, (x a b * y c d) • (E a b * E c d) := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
      exact (swap4 fun a b c d => (x a b * y c d) • (E a b * E c d)).symm
    have hYX : (∑ c, ∑ d, y c d • E c d) * (∑ a, ∑ b, x a b • E a b) =
        ∑ a, ∑ b, ∑ c, ∑ d, (x a b * y c d) • (E c d * E a b) := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, mul_comm (y _ _)]
    have hA : ∑ a, ∑ b, ∑ c, ∑ d, (x a b * y c d) • (if b = c then E a d else 0) =
        ∑ a, ∑ d, (∑ c, x a c * y c d) • E a d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      calc _ = ∑ d, ∑ b, ∑ c, (x a b * y c d) • (if b = c then E a d else 0) :=
              (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
        _ = _ := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_smul]
    have hB : ∑ a, ∑ b, ∑ c, ∑ d, (x a b * y c d) • (if d = a then E c b else 0) =
        ∑ a, ∑ d, (∑ c, y a c * x c d) • E a d := by
      rw [swap4]
      refine Finset.sum_congr rfl fun c _ => ?_
      calc _ = ∑ d, ∑ b, ∑ a, (x a b * y c d) • (if d = a then E c b else 0) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ d, ∑ b, (x d b * y c d) • E c b := by
          simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        _ = _ := by
          rw [Finset.sum_comm]; simp only [Finset.sum_smul, mul_comm (x _ _)]
    change ∑ a, ∑ b, (x * y - y * x) a b • E a b =
      (∑ a, ∑ b, x a b • E a b) * (∑ c, ∑ d, y c d • E c d) - (∑ c, ∑ d, y c d • E c d) * (∑ a, ∑ b, x a b • E a b)
    simp only [Matrix.sub_apply, Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib]
    rw [hXY, hYX, ← hA, ← hB]
    have hE' : ∀ a b c d, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := hE
    simp only [← Finset.sum_sub_distrib, ← smul_sub, hE']

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

abbrev Ugl (N : ℕ) : Type := UniversalEnvelopingAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ)

def Eu (N : ℕ) (a b : Fin N) : Ugl N := UniversalEnvelopingAlgebra.ι ℂ (Matrix.single a b (1 : ℂ))

end GlobalTheory.CapelliUniv
