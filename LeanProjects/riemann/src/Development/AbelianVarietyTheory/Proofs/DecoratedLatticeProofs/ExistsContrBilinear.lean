import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhat
open MeasureTheory Matrix ValuativeRel GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LocFlat.ContrBil
open GlobalTheory.LocFlat.LastColumn

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {f : Y → ℂ} (hf : f ∈ SB Y)
    {i : X → Y} (hi : Continuous i) {r : Y → X} (hr : Continuous r) (hri : ∀ x, r (i x) = x) :
    (fun x => f (i x)) ∈ SB X := by
  refine ⟨hf.1.comp_continuous hi, HasCompactSupport.intro (hf.2.image hr) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, hri x⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

end GlobalTheory.LocFlat.ContrBil
