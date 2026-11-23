import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf
open Matrix NumberField
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatticeCoordinateLemmas

variable {D : D7} (X : HidaSetting D)

def gv (v : Fin X.B.I.n → X.B.I.E) : (VS D).V := X.bas.equivFun.symm (fun i => X.ιE (v i))

theorem crd_gv (v : Fin X.B.I.n → X.B.I.E) : X.crd (gv X v) = v := by
  funext i
  show X.ιE.symm (X.bas.repr (X.bas.equivFun.symm (fun i => X.ιE (v i))) i) = v i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]

theorem gv_crd (y : (VS D).V) : gv X (X.crd y) = y := by
  show X.bas.equivFun.symm (fun i => X.ιE (X.ιE.symm (X.bas.repr y i))) = y
  simp only [RingEquiv.apply_symm_apply, ← Module.Basis.equivFun_apply]
  exact X.bas.equivFun.symm_apply_apply y

abbrev sO : 𝓞 D.host.E →+* 𝓞 X.B.I.E := (RingOfIntegers.mapRingEquiv X.ιE.symm : 𝓞 D.host.E →+* 𝓞 X.B.I.E)

abbrev sO' : 𝓞 X.B.I.E →+* 𝓞 D.host.E := (RingOfIntegers.mapRingEquiv X.ιE : 𝓞 X.B.I.E →+* 𝓞 D.host.E)

abbrev sE : X.B.I.E →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E)

def crdO : (VS D).V →ₛₗ[sO X] (Fin X.B.I.n → X.B.I.E) where
  toFun := X.crd
  map_add' y z := by
    funext i
    show X.ιE.symm (X.bas.repr (y + z) i) = X.ιE.symm (X.bas.repr y i) + X.ιE.symm (X.bas.repr z i)
    rw [map_add, Finsupp.add_apply, map_add]
  map_smul' a y := by
    funext i
    show X.ιE.symm (X.bas.repr (a • y) i) = (sO X a) • X.ιE.symm (X.bas.repr y i)
    have ha : a • y = (a : D.host.E) • y := (algebraMap_smul D.host.E a y).symm
    rw [ha, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    rfl

def gvO : (Fin X.B.I.n → X.B.I.E) →ₛₗ[sO' X] (VS D).V where
  toFun := gv X
  map_add' v w := by
    show X.bas.equivFun.symm (fun i => X.ιE ((v + w) i)) =
      X.bas.equivFun.symm (fun i => X.ιE (v i)) + X.bas.equivFun.symm (fun i => X.ιE (w i))
    rw [← map_add]
    congr 1
    funext i
    simp [map_add]
  map_smul' c v := by
    show X.bas.equivFun.symm (fun i => X.ιE ((c • v) i)) = (sO' X c) • X.bas.equivFun.symm (fun i => X.ιE (v i))
    have hc : (sO' X c) • X.bas.equivFun.symm (fun i => X.ιE (v i)) =
        ((sO' X c : 𝓞 D.host.E) : D.host.E) • X.bas.equivFun.symm (fun i => X.ιE (v i)) :=
      (algebraMap_smul D.host.E (sO' X c) _).symm
    rw [hc, ← map_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def, map_mul]
    rfl

def gvE : (Fin X.B.I.n → X.B.I.E) →ₛₗ[sE X] (VS D).V where
  toFun := gv X
  map_add' v w := by
    show X.bas.equivFun.symm (fun i => X.ιE ((v + w) i)) =
      X.bas.equivFun.symm (fun i => X.ιE (v i)) + X.bas.equivFun.symm (fun i => X.ιE (w i))
    rw [← map_add]
    congr 1
    funext i
    simp [map_add]
  map_smul' c v := by
    show X.bas.equivFun.symm (fun i => X.ιE ((c • v) i)) = (sE X c) • X.bas.equivFun.symm (fun i => X.ιE (v i))
    rw [← map_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rfl

end LatticeCoordinateLemmas

open LatticeCoordinateLemmas in

theorem latOfLattice_holds {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : LatOfLattice X u := by
  intro h
  haveI : RingHomSurjective (sO' X) := ⟨(RingOfIntegers.mapRingEquiv X.ιE).surjective⟩
  haveI : RingHomSurjective (sE X) := ⟨X.ιE.surjective⟩
  obtain ⟨hfg, hspan⟩ := PIW.AdelClassFin.mLat_of PIW.AdelClassFin.lattice_intersection'
    PIW.AdelClassFin.lattice_denominator X.B.I ((h : X.B.I.Gf) * X.xu u)
  refine ⟨(PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u)).map (gvO X), ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      show X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (gv X v)) ∈ X.B.I.Lf
      rw [crd_gv]
      exact hv
    · intro hy
      exact ⟨X.crd y, hy, gv_crd X y⟩
  · refine ⟨hfg.map _, ?_⟩
    rw [Submodule.map_coe, show ⇑(gvO X) = ⇑(gvE X) from rfl, Submodule.span_image, hspan,
      Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨X.crd y, gv_crd X y⟩

end Formalism.L2.SG.PoincareInHH.Cut
