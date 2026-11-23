import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection
import Mathlib.AlgebraicGeometry.Sites.Proetale

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection

namespace LateralTheory.E.LeafKumFieldPf.GmSecSurj

def unitsEquivHom (A : Type) [CommRing A] : (Multiplicative ℤ →* A) ≃ Aˣ where
  toFun f := (zpowersHom Aˣ).symm f.toHomUnits
  invFun u := (Units.coeHom A).comp (zpowersHom Aˣ u)
  left_inv f := by ext; simp
  right_inv u := by ext; simp

abbrev LR : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra ℤ ℤ)

def homUnits (A : CommRingCat.{0}) : (LR ⟶ A) ≃ Aˣ :=
  ({ toFun := fun f => f.hom, invFun := CommRingCat.ofHom, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl } : (LR ⟶ A) ≃ (AddMonoidAlgebra ℤ ℤ →+* A)).trans <|
    (RingHom.equivIntAlgHom _ _).trans <| (AddMonoidAlgebra.lift ℤ A ℤ).symm.trans (unitsEquivHom A)

theorem homUnits_val (A : CommRingCat.{0}) (ψ : LR ⟶ A) :
    ((homUnits A ψ : Aˣ) : A) = ψ.hom (AddMonoidAlgebra.of ℤ ℤ (Multiplicative.ofAdd 1)) := by
  simp [homUnits, unitsEquivHom]
  rfl

theorem homUnits_nat {A B : CommRingCat.{0}} (ψ : LR ⟶ A) (h : A ⟶ B) :
    homUnits B (ψ ≫ h) = Units.map h.hom.toMonoidHom (homUnits A ψ) := by
  ext
  simp [homUnits_val]

abbrev P : Scheme.{0}ᵒᵖ ⥤ Type 1 := Scheme.Γ ⋙ unitsF ⋙ forget _

def repr : P.RepresentableBy (Spec LR) where
  homEquiv {X} := (ΓSpec.adjunction.homEquiv X (op LR)).symm.trans <|
    ({ toFun := fun φ => φ.unop, invFun := fun φ => φ.op, left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      (Scheme.Γ.rightOp.obj X ⟶ op LR) ≃ (LR ⟶ Γ(X, ⊤))).trans <| (homUnits _).trans <|
      Additive.ofMul.trans Equiv.ulift.symm
  homEquiv_comp {X X'} f g := by
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact congrArg (fun u => ULift.up (Additive.ofMul u)) (homUnits_nat _ (Scheme.Γ.map f.op))

theorem isSheaf_P : Presieve.IsSheaf Scheme.etaleTopology.{0} P := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have : P.IsRepresentable := repr.isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

theorem isSheaf_units : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF) :=
  (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_P)

theorem LeafGmSecSurj_of : LateralTheory.E.H2CurveOrder.KummerH0Surjection.LeafGmSecSurj := by
  intro B _ y
  have := isIso_toSheafify Scheme.etaleTopology.{0} isSheaf_units
  let g := (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op (Spec (CommRingCat.of B)))
  refine ⟨((inv g).hom y).down, ?_⟩
  show g.hom ((inv g).hom y) = y
  change (inv g ≫ g).hom y = y
  rw [IsIso.inv_hom_id]
  rfl

end LateralTheory.E.LeafKumFieldPf.GmSecSurj
