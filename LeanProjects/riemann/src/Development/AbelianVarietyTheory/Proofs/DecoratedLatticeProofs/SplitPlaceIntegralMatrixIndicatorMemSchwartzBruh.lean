import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.LocMod.Place

theorem intInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'],
    Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  intro k _ _ _ _ Y Y' _ _ _ _
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  set K : Set (Matrix Y Y' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hK
  have hKeq : K = Set.univ.pi fun _ : Y => Set.univ.pi fun _ : Y' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ r) q (Set.mem_univ q)⟩
  have hKo : IsOpen K := by
    rw [hKeq]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hKc : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have hcl : IsClosed K := by
    rw [hKeq]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (Valuation.isClosed_integer (v := valuation k))
  refine ⟨?_, ?_⟩
  · show IsLocallyConstant (K.indicator fun _ => (1 : ℂ))
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · show HasCompactSupport (K.indicator fun _ => (1 : ℂ))
    exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LocMod.Place
