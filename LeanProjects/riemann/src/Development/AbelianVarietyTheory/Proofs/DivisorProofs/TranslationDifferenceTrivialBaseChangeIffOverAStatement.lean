import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverA
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.triv_twist_iff | exact GlobalTheory.TwistFlat.triv_twist_iff | (intros; apply GlobalTheory.TwistFlat.triv_twist_iff <;> assumption)
