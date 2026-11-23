import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem coreOnto_of_chain (hO : ∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) (hC : ComOK) (hS : StageOK) (hE : ChainEx) (hT : TopCols) :
    CoreOnto := by
  intro D hq hsz T L μ0 hL sc hgap G W M hM v MP _hcart y hy x hx
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  obtain ⟨⟨r₀, hr₀⟩, hst₀⟩ := hS D hq T L μ0 hL sc G W M hM 0 (Nat.zero_le _)
  obtain ⟨r, Mm, _hr, Θ, hR, hB⟩ := hE D hq hsz T L μ0 hL sc hgap G W M hM v r₀ MP hr₀ D.R.m le_rfl
  have hcom : (gridCom W).Is := hC D hq hsz T L μ0 hL sc hgap G W M hM
  have hs0 : (gridStage G v 0 r₀ MP).Is (gridCom W) 0 := hst₀ r₀ hr₀ v MP
  have hsurj := hO D (gridCom W) hcom (gridStage G v 0 r₀ MP) hs0 D.R.m le_rfl _ Θ hR
  have hyCC : y ∈ (gridStage G v 0 r₀ MP).CC (gridCom W) := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).1
    exact (SetLike.ext_iff.mp h y).mpr hy
  obtain ⟨y', hy'⟩ := hsurj ⟨y, hyCC⟩
  have hx' : x ∈ (gridStage G v 0 r₀ MP).KF := by
    have h := (hRL.2.1 (G.V (.core 0)) r₀ W.θ _ MP (lev G (.core 0) : Set _)).2.1
    rw [← h] at hx
    exact hx
  have key := hB y' x hx'
  rw [hy'] at key
  refine Submodule.span_mono ?_ key
  rintro F₀ ⟨w, Ψ, hrap, hstep, h0, hm⟩
  refine ⟨Ψ, ⟨hrap, hstep⟩, h0, ?_⟩
  have htop : y'.1 ∈ CoreForms G W.θ D.R.m Mm := by
    have h := (hRL.2.1 (G.V (.core D.R.m)) r W.θ _ Mm (lev G (.core D.R.m) : Set _)).1
    exact (SetLike.ext_iff.mp h y'.1).mp y'.2
  obtain ⟨c, hc, ξ, hξ⟩ := hT D hq T L μ0 hL sc G W M hM Mm _ htop w
  exact ⟨c, hc, ξ, hm.trans hξ⟩

end GlobalTheory.CoreOnto

end
