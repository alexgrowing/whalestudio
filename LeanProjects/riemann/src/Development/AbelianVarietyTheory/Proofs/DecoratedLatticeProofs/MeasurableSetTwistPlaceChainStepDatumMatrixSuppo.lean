import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
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

noncomputable section

namespace GlobalTheory.NrmVol

theorem measurableSet_suppQ : ∀ (D : D7) (v : FinPl D) (a b r : ℕ),
    MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  intro D v a b r
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv D.host.F v)
  haveI : OpensMeasurableSpace (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
    inferInstanceAs (OpensMeasurableSpace (Fin b → Fin a → Fv D.host.F v))
  have hentry : ∀ i j, Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have htop : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => topL r x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold topL
    by_cases h : i.val < b ∧ j.val < a
    · simp only [dif_pos h]; exact hentry _ _
    · simp only [dif_neg h]; exact continuous_const
  have hdet : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => (topL r x).det :=
    htop.matrix_det
  have hball : IsOpen {y : Fv D.host.F v | Valued.v y < 1} := by
    simpa using Valued.isOpen_ball (Fv D.host.F v) 1
  have hsph : IsOpen {y : Fv D.host.F v | Valued.v y = 1} := by
    simpa using Valued.isOpen_sphere (Fv D.host.F v) (r := 1) one_ne_zero
  have hcb : IsOpen {y : Fv D.host.F v | Valued.v y ≤ 1} := by
    simpa using Valued.isOpen_closedBall (Fv D.host.F v) (r := 1) one_ne_zero
  have h1 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} =
        (fun x => (topL r x).det) ⁻¹' {0}ᶜ := by
      ext x; simp [isUnit_iff_ne_zero]
    rw [this]
    exact (isOpen_compl_singleton.preimage hdet).measurableSet
  have h2 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | Valued.v (topL r x).det = 1} :=
    (hsph.preimage hdet).measurableSet
  have h3 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} =
        ⋂ i, ⋂ j, (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (hcb.preimage (hentry i j)).measurableSet
  have h4 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
        ⋂ i, ⋂ j, {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : r ≤ i.val ∧ j.val < r
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y < 1} := by
        ext x; simp [hij.1, hij.2]
      rw [this]
      exact (hball.preimage (hentry i j)).measurableSet
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h h'
        exact absurd ⟨h, h'⟩ hij
      rw [this]
      exact MeasurableSet.univ
  have : suppQ (a := a) (b := b) v r =
      {x | IsUnit (topL r x).det} ∩ {x | Valued.v (topL r x).det = 1} ∩
        {x | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} ∩
        {x | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    ext x
    simp only [suppQ, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

end GlobalTheory.NrmVol
