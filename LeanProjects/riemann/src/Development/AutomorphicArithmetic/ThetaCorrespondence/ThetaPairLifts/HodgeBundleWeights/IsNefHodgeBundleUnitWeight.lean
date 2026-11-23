import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNefStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefUnit
open GlobalTheory.FlagMod (FlagCover Frames ev ev_res ev_spMap ext_ev tau tau_le spMap_ev ev_tau le_preimage_comp le_preimage_mono
  vec tanPull tanPull_actR tanPull_vec tan_ext_left ev_pull_g)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt IsCombAt IsFrame chi compactOf toF)
open GlobalTheory.DetLine (FrY RuleY SecY NzY)
section Glue
variable {W : Scheme.{0}}
end Glue
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)
theorem isNef_hodgeBundle_unitWeight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF τ
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hp := (VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  exact ⟨(isGenerated_unitWt hP.p1 TF Z hF τ 1).isNef_of_isProjOver hp,
    (isGenerated_unitWt hP.p1 TF Z hF τ (-1)).isNef_of_isProjOver hp⟩
end GlobalTheory.NefUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_unitWeight_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  first | exact @_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | exact _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | (intros; apply _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight <;> assumption)
end
