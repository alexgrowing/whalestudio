import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen : ∀ {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h] (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens), Ω₁.1 ≤ h ⁻¹ᵁ U.1 → Ω₂.1 ≤ h ⁻¹ᵁ U.1 → IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  first | exact @GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | exact GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | (intros; apply GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage <;> assumption)
