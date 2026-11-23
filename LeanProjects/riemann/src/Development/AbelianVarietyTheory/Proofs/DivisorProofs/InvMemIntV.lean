import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

abbrev Qv (v : AwayP p) : Type := v.1.adicCompletion ℚ

abbrev Gv (G : HTGroup p) (v : AwayP p) : Type := UPts G.star (Qv v)

def piV (G : HTGroup p) (v : AwayP p) : G.GAf →* Gv G v := ubcMap (AfP.eval v)

def basV (G : HTGroup p) (v : AwayP p) : Module.Basis (Fin (Module.finrank ℚ G.C)) (Qv v) (Qv v ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (Qv v) (Module.finBasis ℚ G.C)

def IsIntV (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) : Prop :=
  ∀ i, (basV G v).repr y i ∈ v.1.adicCompletionIntegers ℚ

def IntV (G : HTGroup p) (v : AwayP p) : Set (Gv G v) :=
  {g | IsIntV G v (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    IsIntV G v ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ) ∧
    (((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ)}

theorem inv_mem_IntV (G : HTGroup p) (v : AwayP p) {g : Gv G v} (h : g ∈ IntV G v) : g⁻¹ ∈ IntV G v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h2
  · simpa using h1
  · exact h4
  · simpa using h3

end GlobalTheory.OrbFinAf
