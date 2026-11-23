import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

section Defs
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)

abbrev bc : Over (Sp V) := (Over.pullback (φ ≫ T.hom)).obj A

abbrev bcR : Over (Sp R) := Over.mk ((bc A φ).hom ≫ φ ≫ T.hom)

def pa : bcR A φ ⟶ A := Over.homMk (pullback.fst A.hom (φ ≫ T.hom)) (by
  show pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = pullback.snd A.hom (φ ≫ T.hom) ≫ φ ≫ T.hom
  exact pullback.condition)

def pt : bcR A φ ⟶ T := Over.homMk ((bc A φ).hom ≫ φ) (Category.assoc _ _ _)

def twist (N : LB (A ⊗ T).left) : LB (bcR A φ).left := N.pull (lift (pa A φ) (pt A φ)).left

abbrev ker {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : Over (Sp V) := Over.mk (pullback.snd (h ≫ snd A T).left φ)

def kerι {H : Over (Sp R)} (h : H ⟶ A ⊗ T) : ker A φ h ⟶ bc A φ :=
  Over.homMk (pullback.lift (pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left) (pullback.snd _ _) (by
    have w : (h ≫ fst A T).left ≫ A.hom = (h ≫ snd A T).left ≫ T.hom := by rw [Over.w, Over.w]
    rw [Category.assoc, w, pullback.condition_assoc])) (pullback.lift_snd _ _ _)

variable {A}

abbrev up (Y : Over (Sp V)) : Over (Sp R) := Over.mk (Y.hom ≫ φ ≫ T.hom)

def upa {Y : Over (Sp V)} (x : Y ⟶ bc A φ) : up φ Y ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ φ ≫ T.hom) (Over.w x))

def upt (Y : Over (Sp V)) : up φ Y ⟶ T := Over.homMk (Y.hom ≫ φ) (Category.assoc _ _ _)

end Defs
end GlobalTheory.TwistFlat
