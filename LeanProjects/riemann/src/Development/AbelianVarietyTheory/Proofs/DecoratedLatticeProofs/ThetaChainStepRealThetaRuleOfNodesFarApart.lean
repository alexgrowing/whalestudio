import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.ChainParOfGap

theorem chainPar_of_nodeGap : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ k, ChainPar D k := by
  intro D h k
  unfold GlobalTheory.Chain.ChainPar
  intro τ
  obtain ⟨al, be, ga, de, hc, h1, h2⟩ := GlobalTheory.ArchRec.ParChain.parChain D k τ
  unfold GlobalTheory.ArchRec.Centred at hc
  unfold Formalism.MainNotions.SchurIrreducible.DataAR
  refine ⟨al, be, ga, de, ⟨hc.1, hc.2.2 h⟩, hc.2.1, ?_, ?_⟩
  · rw [h1]
    clear hc h1 h2 h
    congr 1
    unfold expT GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alT
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
  · rw [h2]
    clear hc h1 h2 h
    congr 1
    unfold expS GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alS
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring

end GlobalTheory.Corev.ChainParOfGap
