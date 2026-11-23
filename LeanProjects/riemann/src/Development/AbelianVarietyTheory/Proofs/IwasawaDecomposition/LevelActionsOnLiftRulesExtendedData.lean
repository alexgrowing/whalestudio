import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
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
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.ActExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def LevB (D : D7) (i : Fin D.R.m) (Pg : Finset (Pl D.host.E)) (β : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (io : La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
      (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
    ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (Formalism.IndefR.FWT.rank_Wc i)) ∘ₗ io) (lev g a)) -
        (finHom (Wc D i) κ).1.mulVec (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (Formalism.IndefR.FWT.rank_Wc i)) ∘ₗ io) a)) = M • w

theorem act_heq (D : D7) (i : Fin D.R.m) (n : ℕ) {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {l' : Level H'}
    {c : Coeff l} {c' : Coeff l'} {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {io : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {io' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    {Pg Pg' : Finset (Pl D.host.E)} {β β' : ∀ i, GL (Fin (Wc D i).rank) (EAf D)} {G : Type} [Group G]
    {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r}
    {lev : G → (Dw n).La →ₗ[𝓞 D.host.E] (Dw n).La} {lev' : G → (Dw' n).La →ₗ[𝓞 D.host.E] (Dw' n).La}
    (hH : HEq H' H) (hl : HEq l' l) (hc : HEq c' c) (hD : HEq Dw' Dw) (hX : HEq Xo' Xo) (hi : HEq io' io)
    (hP : HEq Pg' Pg) (hβ : HEq β' β) (he : HEq eG' eG) (hA : l.A = 1)
    (hU : ∀ lev lev' : G → (Dw n).La →ₗ[𝓞 D.host.E] (Dw n).La, LevB D i Pg β eG (io n) l.M (Mfr l) lev →
      LevB D i Pg β eG (io n) l.M (Mfr l) lev' → ∀ g a, lev g a - lev' g a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw n).La))
    (h : LevB D i Pg β eG (io n) l.M (Mfr l) lev) (h' : LevB D i Pg' β' eG' (io' n) l'.M (Mfr l') lev')
    (g g' : G) (hg : HEq g' g) (r : Rul (Xo n) c) (r' : Rul (Xo' n) c') (hr : HEq r' r) :
    HEq (actLev c' (fun g => (lev' g, LinearMap.id)) g' r') (actLev c (fun g => (lev g, LinearMap.id)) g r) := by
  obtain rfl := eq_of_heq hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hβ
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hr
  rw [GlobalTheory.OneMapAllCompare.actLev_congr (lev := fun g => (lev' g, LinearMap.id)) (lev' := fun g => (lev g, LinearMap.id)) c' hA
    (hU lev' lev h' h)]

end GlobalTheory.Mem.R3.ActExt
end
