import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslati
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.same_lam_iff_locally_triv | exact GlobalTheory.TwistFlat.same_lam_iff_locally_triv | (intros; apply GlobalTheory.TwistFlat.same_lam_iff_locally_triv <;> assumption)
