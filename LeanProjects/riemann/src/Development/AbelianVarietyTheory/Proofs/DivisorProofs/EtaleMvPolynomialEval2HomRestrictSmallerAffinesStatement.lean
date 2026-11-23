import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffines
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
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
theorem _root_.GlobalTheory.T.etale_mvPolynomial_eval2Hom_restrict_smaller_affines : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  first | exact @GlobalTheory.EtaleRestrict.etale_eval₂_res | exact GlobalTheory.EtaleRestrict.etale_eval₂_res | (intros; apply GlobalTheory.EtaleRestrict.etale_eval₂_res <;> assumption)
