import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem closure_point_topologicalKrullDim : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  intro X n z hX
  set S : Set X := closure ({z} : Set X) with hS
  have hle : topologicalKrullDim S ≤ n := hX ▸ topologicalKrullDim_subspace_le X S
  have hzS : z ∈ S := subset_closure rfl
  haveI : Nonempty S := ⟨⟨z, hzS⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {(⟨z, hzS⟩ : S)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e := by
    generalize topologicalKrullDim S = d at hle h0 ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m => exact ⟨m, rfl⟩
  refine ⟨e, ?_, he, ?_⟩
  · rw [he] at hle; exact_mod_cast hle
  · intro x hzx hxz
    have hxS : x ∈ S := specializes_iff_mem_closure.mp hzx
    let x' : S := ⟨x, hxS⟩
    let z' : S := ⟨z, hzS⟩
    have hsp : z' ⤳ x' := (Topology.IsInducing.subtypeVal.specializes_iff).mp hzx
    have hns : ¬ x' ⤳ z' := fun h => hxz (congrArg Subtype.val (h.antisymm hsp).eq)
    let A : IrreducibleCloseds S := ⟨closure {x'}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds S := ⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {z'}
        exact specializes_iff_closure_subset.mp hsp
      · intro h
        apply hns
        have : closure ({x'} : Set S) = closure {z'} :=
          congrArg (fun C : IrreducibleCloseds S => (C : Set S)) h
        exact specializes_iff_closure_subset.mpr this.symm.subset
    have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.one_le_krullDim_iff.mpr ⟨A, B, hAB⟩
    rw [he] at h1
    exact_mod_cast h1

end GlobalTheory
