import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.valNil :
    UpperTheory.Zero.ConvolutionTheory.EB.ValNil := by
  intro E _ _ _ n Z T S D B₁ B₂ e₁ e₂ hS hZ hT hd hB
  obtain ⟨-, hc, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hoff : ∀ w ∈ T, Off Z w ∧ Off Z (cPl w) := by
    intro w hw
    have h₁ : w ∉ Z := Finset.disjoint_left.mp hd hw
    have h₂ : cPl w ∉ Z := by
      intro h
      obtain ⟨hs, hsp⟩ := hZ _ h
      have hne : cPl (cPl w) ≠ cPl w := ((hc (cPl w)).2).mp hsp
      rw [(hc w).1] at hne
      exact hne ((hsec S hS w).2 (hT w hw) hs).symm
    exact ⟨⟨h₁, h₂⟩, h₂, by rwa [(hc w).1]⟩
  have hz : ∀ w, Off Z w → B₂ w = 0 := fun w hw =>
    Multiset.card_eq_zero.mp (UpperTheory.Zero.ConvolutionTheory.EB.satCard E 0 D w _ (hB w hw))
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
  refine Finset.prod_congr rfl fun w hw => ?_
  obtain ⟨h₁, h₂⟩ := hoff w hw
  rw [hz w h₁, hz _ h₂]
  rfl
