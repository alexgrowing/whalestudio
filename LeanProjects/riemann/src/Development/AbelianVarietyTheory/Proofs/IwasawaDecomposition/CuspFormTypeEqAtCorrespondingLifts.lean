import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

open Classical in

noncomputable def wtPre (P : Pre) (j : ℕ) (aP : Tau P.R → Fin (P.R.sigW j).1 → ℕ) (aM : Tau P.R → Fin (P.R.sigW j).2 → ℕ)
    (x : (P.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : Tau P.R, ((if x.1 = P.host.emb t.1 then Formalism.L2.Pj.ext0 (aP t) x.2 else 0) +
    if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (P.host.emb t.1) then Formalism.L2.Pj.ext0 (aM t) x.2 else 0)

theorem cusp_type_congr {P₁ P₂ : Pre} (hP : P₂ = P₁)
    {H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₁.host.E} {H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₂.host.E}
    {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁} {c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {Xo₁ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₁ j) l₁} {Xo₂ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₂ j) l₂}
    {U₁ : ∀ j (σ : c₁.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₁ j) c₁ σ P₁.R.r}
    {U₂ : ∀ j (σ : c₂.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₂ j) c₂ σ P₂.R.r}
    {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    {aP₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).1 → ℕ} {aP₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).1 → ℕ}
    {aM₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).2 → ℕ} {aM₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).2 → ℕ}
    {n₁ n₂ : ℕ} (hn : n₂ = n₁)
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hDw : HEq Dw₂ Dw₁) (hXo : HEq Xo₂ Xo₁) (hU : HEq U₂ U₁)
    (haP : HEq aP₂ aP₁) (haM : HEq aM₂ aM₁) :
    ↥(Formalism.L2.Pj.cusp (Xo₂ j₂) c₂ (U₂ j₂) (wtPre P₂ j₂ aP₂ aM₂) n₂) =
      ↥(Formalism.L2.Pj.cusp (Xo₁ j₁) c₁ (U₁ j₁) (wtPre P₁ j₁ aP₁ aM₁) n₁) := by
  subst hP hj hn
  cases hH; cases hl; cases hc; cases hDw; cases hXo; cases hU; cases haP; cases haM
  rfl

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem Ext.cuspA_type_eq : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX i₁ i₂ hi
  have hk := hX.κ i₁ i₂ hi
  exact (cusp_type_congr hE.left (congrArg (fun x ↦ x + 1) hi) hk.right.right hX.H hX.l hX.c hX.Dw hX.Xo hX.U hk.left hk.right.left)

end GlobalTheory.Mem.R3.Rw
