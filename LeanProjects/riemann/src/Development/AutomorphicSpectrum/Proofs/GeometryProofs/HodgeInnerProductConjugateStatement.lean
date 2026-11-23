import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugate
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ t.G) (c : ℂ), v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left → HodgeIP t.G t.PP.L z v w c → HodgeIP t.G t.PP.L (spMap (starRingEnd ℂ) ≫ z) v' w' (starRingEnd ℂ c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeConj.hodgeInnerProduct_conj_abelianScheme | exact GlobalTheory.CompanionTheory.Ar.HodgeConj.hodgeInnerProduct_conj_abelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeConj.hodgeInnerProduct_conj_abelianScheme <;> assumption)
