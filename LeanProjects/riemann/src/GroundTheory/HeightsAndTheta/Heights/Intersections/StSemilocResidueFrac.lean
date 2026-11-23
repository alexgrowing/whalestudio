import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem primeSubfield_exists_div {E : Type*} [Field E] (c : (⊥ : Subfield E)) :
    ∃ a b : ℤ, (b : (⊥ : Subfield E)) ≠ 0 ∧ c = a / b := by
  have hc : (c : E) ∈ Subfield.closure (∅ : Set E) := by
    rw [Subfield.closure_empty]
    exact c.2
  obtain ⟨y, hy, z, hz, h⟩ := Subfield.mem_closure_iff.1 hc
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : (b : E) = 0
  · refine ⟨0, 1, by simp, Subtype.ext ?_⟩
    simp [← h, hb]
  · refine ⟨a, b, fun h0 => hb ?_, Subtype.ext ?_⟩
    · simpa using congrArg Subtype.val h0
    · simp [← h]

def SemilocResidueFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    ∀ (F : Type) [Field F] [Algebra F G'.Φ'], (∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (IntermediateField.relfinrank
        (IntermediateField.adjoin F
          (Set.range ((fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩)) : ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
