import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section FF

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F') (E : WeierstrassCurve F)

noncomputable def ffMap : E.toAffine.FunctionField →+* (E.map σ).toAffine.FunctionField :=
  letI := σ.toAlgebra
  (bcEmb (F' := F') E).toRingHom

theorem ffMap_genX : ffMap σ E (genX E) = genX (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genX (F' := F') E

theorem ffMap_genY : ffMap σ E (genY E) = genY (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genY (F' := F') E

theorem ffMap_algebraMap (a : F) :
    ffMap σ E (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F' (E.map σ).toAffine.FunctionField (σ a) := by
  let _ := σ.toAlgebra
  exact (bcEmb (F' := F') E).commutes a

theorem ringHom_ext_functionField {W : WeierstrassCurve F} {L : Type*} [Field L]
    {f g : W.toAffine.FunctionField →+* L}
    (hc : ∀ a : F, f (algebraMap F _ a) = g (algebraMap F _ a)) (hx : f (genX W) = g (genX W))
    (hy : f (genY W) = g (genY W)) : f = g := by
  let _ : Algebra F L := (f.comp (algebraMap F W.toAffine.FunctionField)).toAlgebra
  let f' : W.toAffine.FunctionField →ₐ[F] L := { f with commutes' := fun a => rfl }
  let g' : W.toAffine.FunctionField →ₐ[F] L := { g with commutes' := fun a => (hc a).symm }
  have e : f' = g' := algHom_ext_gen W hx hy
  ext z
  exact DFunLike.congr_fun e z

noncomputable def ffCongr {C D : WeierstrassCurve F'} (h : C = D) :
    C.toAffine.FunctionField ≃+* D.toAffine.FunctionField := by
  subst h; exact RingEquiv.refl _

theorem ffCongr_genX {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genX C) = genX D := by
  subst h; rfl

theorem ffCongr_genY {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genY C) = genY D := by
  subst h; rfl

theorem ffCongr_algebraMap {C D : WeierstrassCurve F'} (h : C = D) (a : F') :
    ffCongr h (algebraMap F' C.toAffine.FunctionField a) = algebraMap F' D.toAffine.FunctionField a := by
  subst h; rfl

end FF

section Map

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.val_eq (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  rcases φ with ⟨Q, ⟨x, y, h, rfl, hx⟩, hr⟩
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ext_xy {φ ψ : Isogeny E E'} (hx : φ.x = ψ.x) (hy : φ.y = ψ.y) : φ = ψ := by
  apply Isogeny.ext'
  rw [φ.val_eq, ψ.val_eq]
  simp only [Point.some.injEq]
  exact ⟨hx, hy⟩

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.map (φ : Isogeny E E') : Isogeny (E.map σ) (E'.map σ) :=
  letI := σ.toAlgebra
  letI := Classical.decEq F'
  isogBaseChange (F' := F') φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_x (φ : Isogeny E E') : (φ.map σ).x = ffMap σ E φ.x := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_y (φ : Isogeny E E') : (φ.map σ).y = ffMap σ E φ.y := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comap_map (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    (φ.map σ).comap (ffMap σ E' f) = ffMap σ E (φ.comap f) := by
  have e : (φ.map σ).comap.toRingHom.comp (ffMap σ E') = (ffMap σ E).comp φ.comap.toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_algebraMap,
        AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        Isogeny.comap_genX, Isogeny.map_x]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        Isogeny.comap_genY, Isogeny.map_y]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_alt (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).x = φ.comap ψ.x := by
  rw [Isogeny.x, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_y (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).y = φ.comap ψ.y := by
  rw [Isogeny.y, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).map σ = (ψ.map σ).comp (φ.map σ) := by
  apply Isogeny.ext_xy
  · rw [Isogeny.map_x, Isogeny.comp_alt, Isogeny.comp_alt, Isogeny.map_x, Isogeny.comap_map]
  · rw [Isogeny.map_y, Isogeny.comp_y, Isogeny.comp_y, Isogeny.map_y, Isogeny.comap_map]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).map σ = mulIsogeny (E.map σ) n hn := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := F') E) (n • genericPoint E) =
    n • genericPoint (E.baseChange F')
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

end Map

section Congr

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {C D C' D' C'' D'' : WeierstrassCurve F'} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
  [D'.IsElliptic] [C''.IsElliptic] [D''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : Isogeny D D' := by
  subst hC hC'; exact φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_alt (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').x = ffCongr hC φ.x := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_y (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').y = ffCongr hC φ.y := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_rfl (φ : Isogeny C C') : φ.congr rfl rfl = φ :=
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : (φ.congr hC hC').degree = φ.degree := by
  subst hC hC'; rfl

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : Isogeny D D' :=
  (φ.map σ).congr hE hE'

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_alt (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').x = ffCongr hE (ffMap σ E φ.x) := by
  rw [Isogeny.mapOf, Isogeny.congr_alt, Isogeny.map_x]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_y (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').y = ffCongr hE (ffMap σ E φ.y) := by
  rw [Isogeny.mapOf, Isogeny.congr_y, Isogeny.map_y]

end Congr

end GroundTheory.Global
