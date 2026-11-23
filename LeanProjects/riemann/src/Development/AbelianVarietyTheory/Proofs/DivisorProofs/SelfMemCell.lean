import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : Set (GA E a) :=
  {p | ∃ u ∈ NA E a, ∃ k ∈ K, ∃ y : GL (Fin a) (Cinf E), p = u * q * finGL E a k * infGL E a y}

theorem self_mem_cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : q ∈ cell K q :=
  ⟨1, ⟨fun i j h => by simp [Matrix.one_apply_ne (Fin.ne_of_gt h)], fun i => by simp⟩, 1, K.one_mem, 1, by simp⟩

end GlobalTheory.JSW.MirPatch
