import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitUnr

open GlobalTheory.LFun

theorem unrAt_and_val_inv : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), ResEta D χ 0 → ∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w ≠ w' → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w' ∧ GlobalTheory.LFun.val (F := D.host.F) χ w' = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  intro D χ hr w w' hww hne hu
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  have hres := (GlobalTheory.LFun.resEta_iff χ 0).1 hr
  obtain ⟨⟨η, hη⟩, hμ⟩ := hres
  generalize hv : w'.under (𝓞 D.host.F) = v at hww
  obtain ⟨τ', hτ', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne.symm hv hww
  have key : ∀ a : (Fv D.host.F v)ˣ, locChar χ w' (Units.map (complMap hv).toMonoidHom a) =
      (locChar χ w (Units.map (complMap hww).toMonoidHom a))⁻¹ := by
    intro a
    have e : locIdele D.host.F w (Units.map (complMap hww).toMonoidHom a) *
        locIdele D.host.F w' (Units.map (complMap hv).toMonoidHom a) =
        ideleMap D.host.F D.host.E (Units.map (Algebra.norm (AF D.host.F) : AF D.host.F ⊗[D.host.F] D.host.E →* AF D.host.F)
          (locIdele D.host.F w (Units.map (complMap hww).toMonoidHom a))) :=
      Units.ext (by
        rw [Units.val_mul, ← GlobalTheory.LFun.SplitVal.sigR_locIdele hE hww hv hne]
        exact (GlobalTheory.Doubling.algebraMap_norm_eq hE _).symm)
    have k := congrArg χ e
    rw [hμ η hη, pow_zero, map_mul] at k
    have k2 := (map_mul Circle.toUnits _ _).symm.trans ((congrArg Circle.toUnits k).trans (map_one _))
    exact eq_inv_of_mul_eq_one_right k2
  have hunr : UnrAt χ w' := by
    intro x hx
    set a : (Fv D.host.F v)ˣ := Units.map (ConjPlace.complEquiv hE hv hτ').symm.toRingHom.toMonoidHom x with ha
    have hax : Units.map (complMap hv).toMonoidHom a = x :=
      Units.ext ((ConjPlace.complEquiv hE hv hτ').apply_symm_apply (x : _))
    rw [← hax, key, hu _ ?_, inv_one]
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne hww hv
    unfold Formalism.L2.Host.IsUnitAt at hx ⊢
    have h1 : Valued.v ((complMap hv) (a : Fv D.host.F v)) = 1 := by
      rw [show (complMap hv) (a : Fv D.host.F v) = (x : _) from congrArg Units.val hax]; exact hx
    rw [ConjPlace.valued_complMap hE hv hτ'] at h1
    change Valued.v (complMap hww (a : Fv D.host.F v)) = 1
    rw [ConjPlace.valued_complMap hE hww hτ, h1]
  exact ⟨hunr, eq_inv_of_mul_eq_one_right (ResEta.val_mul_val hE.2.2.1 ((GlobalTheory.LFun.resEta_iff χ 0).1 hr) hne hww hv hu hunr)⟩

end GlobalTheory.SplitUnr

end
