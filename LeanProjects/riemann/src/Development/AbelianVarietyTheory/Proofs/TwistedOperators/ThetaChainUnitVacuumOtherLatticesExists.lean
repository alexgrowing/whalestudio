import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreVacRe

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem reLat_sigOK (G : GridData L sc) (i : ℕ) (h : i ≤ D.R.m) (r : ReLat (G.V (.core i))) : r.sp.SigOK :=
  (G.isV (X := .core i) (by simpa [Node.InRange] using h) (by simp)).sigOK

theorem frameLat_selfDual (V : HSp D) : IsSelfDualC V (GlobalTheory.AdelicU.frameLat V) := by
  have e : GlobalTheory.AdelicU.frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [GlobalTheory.AdelicU.mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [e]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem vacExists_reLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i)))
    (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'),
    ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _)
      (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  intro D _ _ _ _ _ _ G W _ _ i hi r r' S S' M M'
  exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is r.sp r'.sp (cart M) (cart M')
    (reLat_sigOK G i hi.le r) (reLat_sigOK G (i + 1) hi r')
    (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ) (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M' τ)
    _ _ (frameLat_selfDual r.sp) (frameLat_selfDual r'.sp)

end GlobalTheory.CoreVacRe

end
