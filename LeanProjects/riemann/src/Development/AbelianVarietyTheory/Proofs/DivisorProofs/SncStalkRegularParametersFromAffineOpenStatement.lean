import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncStalkRegularParametersFromAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_stalk_regularParameters_from_affineOpen : ∀ (X : Scheme.{0}) (I : X.IdealSheafData), ReciprocityTheory.AnForm.R.FinalTheorems.Snc I → ∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1), IsRegularLocalRing (X.presheaf.stalk x) ∧ ∃ (m : ℕ) (a : Fin m → Γ(X, U.1)) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) m (fun i => (X.presheaf.germ U.1 x hx).hom (a i)) ∧ (I.ideal U).map (X.presheaf.germ U.1 x hx).hom = Ideal.span {(X.presheaf.germ U.1 x hx).hom (∏ i ∈ J, a i)} := by
  first | exact @GlobalTheory.SncStalk.stalk_snc | exact GlobalTheory.SncStalk.stalk_snc | (intros; apply GlobalTheory.SncStalk.stalk_snc <;> assumption)
