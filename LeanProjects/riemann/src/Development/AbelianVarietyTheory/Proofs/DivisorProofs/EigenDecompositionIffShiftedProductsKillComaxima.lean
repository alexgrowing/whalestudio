import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

namespace GlobalTheory.UPel.HT.LieLin

theorem decomp_iff_kill : ∀ (O T V : Type) [CommRing O] [CommRing T] [AddCommGroup V] [Module T V]
  (ψ : O →+* Module.End T V) (a : ℕ)
  (τ : Fin a → (O →+* T)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) → ∀ v : V,
    ((∃ w : Fin a → V, (∀ i, w i ∈ eigSub ψ (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c : Fin a → O, (List.ofFn fun i => ψ (c i) - algebraMap T (Module.End T V) (τ i (c i))).prod v = 0) := by
  intro O T V _ _ _ _ ψ a τ hτ v
  constructor
  · rintro ⟨w, hw, hv⟩ c
    exact GlobalTheory.UPel.HT.LieLoc.kill_of_decomp ψ τ v w (fun i c => mem_eigSub.1 (hw i) c) hv c
  · intro h
    obtain ⟨w, hw, hv⟩ := GlobalTheory.UPel.HT.LieLoc.decomp_of_kill ψ τ hτ v h
    exact ⟨w, fun i => mem_eigSub.2 (hw i), hv⟩

end GlobalTheory.UPel.HT.LieLin
