import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpOfGenericPolarisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PelUnifCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped CategoryTheory.Obj

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (hs : Function.Surjective (G3 G).hom.appTop.hom) {M : RigLB G} (c c' : CubicalStr G M) : c = c' := by
  have h : LB.Gen.Corr M.L _ _ _ _ c.t c'.t :=
    AbLaw.Cube.corr_of_val_section M.isLB hs (lift 1 (lift 1 1))
      (φ := thφ G (x3 G)) (ε := thε) (φ' := thφ G (x3 G)) (ε' := thε) (fun _ _ _ => rfl) c.isGen c'.isGen
      fun _ _ hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm
  have e : c.t = c'.t := TorusExt.gen_ext_val M.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen
    fun _ _ hJ => val_corr hJ h _
  cases c
  cases c'
  cases e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem cubG_heq (P : PELUnif I t) : HEq P.U.cubG t.cub := by
  have := P.U.smooth
  have hs := SymExtend.surjective_cube_of_generic GlobalTheory.globalFns_holds t.G P.A.isAb P.U.gen
  have key : ∀ (M : RigLB t.G) (c : CubicalStr t.G M), M = t.PP → HEq c t.cub := by
    rintro M c rfl
    exact heq_of_eq (cubical_eq hs c t.cub)
  exact key _ _ P.bundle

def pelEquiv (I : Ideal R) (t : SAB H (Sp R)) : PELUnif I t ≃ UniformTorsionIsomorphism.PELUnif I t where
  toFun P :=
    { dat := { D := P.D, mod := P.mod, ac := P.oD, through := (DegActCompare.psiW0_host_iff H P.oD).1 P.w0 }
      unif := { A := P.A, actA := P.oA, U := P.U, LG_eq := P.bundle, cub_eq := cubG_heq P, lin := P.lin } }
  invFun Q :=
    { D := Q.dat.D, mod := Q.dat.mod, oD := Q.dat.ac, A := Q.unif.A, oA := Q.unif.actA, U := Q.unif.U
      bundle := Q.unif.LG_eq, lin := Q.unif.lin
      w0 := (DegActCompare.psiW0_host_iff H Q.dat.ac).2 Q.dat.through }
  left_inv _ := rfl
  right_inv _ := rfl

variable (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev genMap : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)

theorem genMap_cart : IsGrpPullback P.A.A t.G (jK R) (genMap P) := by
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl

abbrev pt (x : TF (R := R) F ⟶ t.G) : TFK (R := R) F ⟶ P.A.A := (pelEquiv I t P).unif.ptA F x

theorem pt_left (x : TF (R := R) F ⟶ t.G) : (pt P F x).left ≫ genMap P = x.left := by
  have hi : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show ((UniformTorsionIsomorphism.toGen x).left ≫ P.U.gen.hom.left) ≫ P.U.gen.inv.left ≫ _ = _
  rw [Category.assoc, ← Category.assoc P.U.gen.hom.left, hi, Category.id_comp]
  exact UniformTorsionIsomorphism.toGen_fst x

theorem ext_genMap {x y : TFK (R := R) F ⟶ P.A.A} (h : x.left ≫ genMap P = y.left ≫ genMap P) : x = y :=
  Over.OverMorphism.ext ((genMap_cart P).1.hom_ext h (by rw [Over.w x, Over.w y]))

def ptEquiv : (TF (R := R) F ⟶ t.G) ≃* (TFK (R := R) F ⟶ P.A.A) :=
  MulEquiv.symm
    { pushHom (genMap_cart P) (TFK (R := R) F) with
      invFun := pt P F
      left_inv := fun _ => ext_genMap P F (pt_left P F _)
      right_inv := fun x => Over.OverMorphism.ext (pt_left P F x) }

def TorsionIsoAt (k : ℕ) : Prop :=
  letI := H.starRing
  ∃ f : QkPt P.D.toPre F k → (TFK (R := R) F ⟶ P.A.A),
    (∀ p x, P.ToA F k p x ↔ x = f p) ∧ (∀ x, x ^ k = 1 → ∃ p, f p = x) ∧
    (∀ p p', f p = f p' ↔ QkPt.Equiv P.D.toPre F p p') ∧
    (∀ p p' p'', Geo.Tor.QkAdd p p' p'' → f p'' = f p * f p') ∧
    (∀ a p p', QkAct P.oD a p p' → f p' = f p ≫ P.oA.act a) ∧
    ∀ p p' (z : Fˣ), WeilQkIs P.D.toPre F k p p' z ↔ WeilIs P.A.A P.A.L k (f p) (f p') (unitOn z)

end GlobalTheory.PelUnifCompare
