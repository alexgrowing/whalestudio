import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology

namespace GlobalTheory.RootEx.OpenKernel

open MeasureTheory ValuativeRel Matrix in
open Filter Topology in

theorem _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by
  by_cases h : ψ = 1
  · subst h
    simp only [AddChar.one_apply, Circle.coe_one]
    exact IsLocallyConstant.const 1
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.SplitWeil.exists_hasConductor_of_continuous ψ hψ h
    exact (_root_.GlobalTheory.SplitWeil.HasConductor.isLocallyConstant hc).comp _

open MeasureTheory ValuativeRel Matrix in
open Filter Topology in

theorem _root_.GlobalTheory.RootEx.OpenKernel.characters_locallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) :=
  fun _ _ _ _ _ => ⟨fun μ hμ => _root_.GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous μ hμ,
    fun ψ hψ => _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ⟩

end GlobalTheory.RootEx.OpenKernel
