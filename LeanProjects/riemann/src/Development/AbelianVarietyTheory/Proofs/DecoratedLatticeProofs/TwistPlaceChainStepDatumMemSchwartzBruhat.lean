import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.SBTwist

theorem viaRed_mem_SB {D : D7} {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ}
    (r : v.adicCompletionIntegers D.host.F →+* k)
    (hr : ∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) :
    GlobalTheory.StepVec.viaRed r ω ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  classical
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : ∀ᶠ y in nhds x, ∀ i j, Valued.v (y i j - x i j) < 1 := by
      rw [Filter.eventually_all]; intro i
      rw [Filter.eventually_all]; intro j
      have hc : Continuous fun y : Matrix (Fin b) (Fin a) (Fv D.host.F v) => y i j :=
        continuous_id.matrix_elem i j
      have hn : {z : Fv D.host.F v | Valued.v (z - x i j) < 1} ∈ nhds (x i j) :=
        Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
      exact hc.continuousAt.preimage_mem_nhds hn
    filter_upwards [hU] with y hy
    have hint : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F ↔ x i j ∈ v.adicCompletionIntegers D.host.F := by
      intro i j
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 := hy i j
      constructor
      · intro h
        have : x i j = y i j - (y i j - x i j) := by ring
        rw [this]
        refine le_trans (Valuation.map_sub _ _ _) (max_le h (le_of_lt h1))
      · intro h
        have : y i j = (y i j - x i j) + x i j := by ring
        rw [this]
        exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt h1) h)
    unfold GlobalTheory.StepVec.viaRed
    by_cases hx : ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F
    · have hy' : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun i j => (hint i j).2 (hx i j)
      rw [dif_pos hy', dif_pos hx]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      have hs : (⟨y i j, hy' i j⟩ : v.adicCompletionIntegers D.host.F) - ⟨x i j, hx i j⟩ =
          ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩ := rfl
      have h0 := (hr ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩).2 (hy i j)
      rw [← hs, map_sub, sub_eq_zero] at h0
      exact h0
    · have hy' : ¬ ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun h => hx fun i j => (hint i j).1 (h i j)
      rw [dif_neg hy', dif_neg hx]
  · haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers D.host.F v
    have hK : IsCompact {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} := by
      have he : {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} =
          Set.pi Set.univ (fun _ : Fin b => Set.pi Set.univ (fun _ : Fin a => (v.adicCompletionIntegers D.host.F : Set (Fv D.host.F v)))) := by
        ext Y
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [he]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 ‹_›
    refine HasCompactSupport.intro hK ?_
    intro Y hY
    have hY' : ¬ ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F := hY
    unfold GlobalTheory.StepVec.viaRed
    exact dif_neg hY'

theorem phiQ_mem_SB : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hφ a b r ξ mu hmu
  obtain ⟨⟨rr, hrr⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hred : GlobalTheory.StepVec.IsRedMap φ PP rr := hrr
  have hmu' : LiftsChar φ PP mu ξ⁻¹⁻¹ := by rwa [inv_inv]
  have heq : phiQ (a := a) (b := b) v r mu = GlobalTheory.StepVec.viaRed rr (GlobalTheory.StepVec.qLoc r PP ξ⁻¹) :=
    funext fun Y => GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc D v φ PP rr hred a b r mu ξ⁻¹ hmu' Y
  rw [heq]
  exact viaRed_mem_SB rr hred.2.1 _

end GlobalTheory.SBTwist
