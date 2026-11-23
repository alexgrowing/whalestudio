import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite

noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  (liesOver_iff_comap_eq _ w).2 rfl

def piPlacesOverEquiv :
    ((v : InfinitePlace K) → PiPlacesOver (L := L) v) ≃ₐ[L] InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩
  invFun y v w := y w
  left_inv x := by
    funext v w
    obtain ⟨w, hw⟩ := w
    have h : w.comap (algebraMap K L) = v := (liesOver_iff_comap_eq v w).1 hw
    subst h
    rfl
  right_inv y := rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' l := rfl

@[simp]
theorem piPlacesOverEquiv_apply (x : (v : InfinitePlace K) → PiPlacesOver (L := L) v)
    (w : InfinitePlace L) :
    piPlacesOverEquiv x w = x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩ := rfl

variable [NumberField K] [NumberField L]

open scoped Classical in

def tensorInfiniteAdeleRingEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L :=
  (Algebra.TensorProduct.piRight K L L (fun v : InfinitePlace K => v.Completion)).trans <|
    (AlgEquiv.piCongrRight fun v => tensorPiEquivLeft (L := L) v).trans piPlacesOverEquiv

theorem tensorInfiniteAdeleRingEquiv_tmul (l : L) (x : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) w =
      (l : w.Completion) * algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by
  change tensorPiEquivLeft (L := L) (w.comap (algebraMap K L))
    (l ⊗ₜ x (w.comap (algebraMap K L))) ⟨w, liesOver_comap w⟩ = _
  rw [tensorPiEquivLeft_tmul]

omit [NumberField K] [NumberField L] in

def infiniteAdeleRingMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (algebraMap (w.comap (algebraMap K L)).Completion w.Completion).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

omit [NumberField K] [NumberField L] in
@[simp]
theorem infiniteAdeleRingMap_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleRingMap x w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := rfl

omit [NumberField K] [NumberField L] in

theorem continuous_infiniteAdeleRingMap :
    Continuous (infiniteAdeleRingMap (K := K) (L := L)) :=
  continuous_pi fun w =>
    (NumberField.LiesOver.continuous_completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (continuous_apply (w.comap (algebraMap K L)))

omit [NumberField K] [NumberField L] in

theorem infiniteAdeleRingMap_algebraMap (k : K) :
    infiniteAdeleRingMap (algebraMap K (InfiniteAdeleRing K) k) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L k) := by
  funext w
  rw [infiniteAdeleRingMap_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply, ← Completion.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L]
  rfl

theorem tensorInfiniteAdeleRingEquiv_tmul' (l : L) (x : InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) =
      algebraMap L (InfiniteAdeleRing L) l * infiniteAdeleRingMap x := by
  funext w
  rw [tensorInfiniteAdeleRingEquiv_tmul]
  rfl

end InfinitePlace

end GroundTheory.Global
