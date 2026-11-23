import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeKeep

variable {D : D7} {V : HSp D}

theorem suppF_iff (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem mt_mul (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := rfl

theorem mt_one : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem fix_mul {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : f • (b - 1) = b - 1) : f • (a * b - 1) = a * b - 1 := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by rw [sub_mul, one_mul]; abel
  rw [e, smul_add, hb, ← smul_mul_assoc, ha]

theorem fix_inv {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : a * b = 1) : f • (b - 1) = b - 1 := by
  have e : b - 1 = -((a - 1) * b) := by rw [sub_mul, one_mul, hb, neg_sub]
  rw [e, smul_neg, ← smul_mul_assoc, ha]

theorem suppF_mul {f : Formalism.L2.Theta.AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  rw [suppF_iff] at ha hb ⊢
  rw [mt_mul]
  exact fix_mul ha hb

theorem suppF_inv {f : Formalism.L2.Theta.AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  rw [suppF_iff] at ha ⊢
  exact fix_inv ha (by rw [← mt_mul, mul_inv_cancel, mt_one])

theorem suppF_one (f : Formalism.L2.Theta.AE D) : SuppF V f 1 := by
  rw [suppF_iff, mt_one, sub_self, smul_zero]

theorem exists_loc (V : HSp D) (f : Formalism.L2.Theta.AE D) : ∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g :=
  ⟨{ carrier := {g | SuppF V f g}, mul_mem' := suppF_mul, one_mem' := suppF_one f, inv_mem' := suppF_inv },
    fun _ => Iff.rfl⟩

end GlobalTheory.HeckeKeep

end
