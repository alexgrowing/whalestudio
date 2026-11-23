import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem redPts_of : RedPts := by
  intro k H X _ _ _ _ _ C ρ h D
  obtain ⟨s, hs⟩ : ∃ s : H ⧸ C → H, Function.RightInverse s C.mkQ :=
    ⟨Function.surjInv (Submodule.mkQ_surjective C), Function.rightInverse_surjInv _⟩
  let g : H ⧸ C → X := fun q => ρ (s q)
  have hg : ∀ a, ρ a = g (C.mkQ a) := by
    intro a
    refine (h _ _).2 ?_
    have h1 : C.mkQ (s (C.mkQ a)) = C.mkQ a := hs _
    have h2 := (Submodule.Quotient.eq C).1 h1
    have h3 : a - s (C.mkQ a) = -(s (C.mkQ a) - a) := by abel
    rw [h3]
    exact C.neg_mem h2
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    have hm := (h _ _).1 hq
    have e := (Submodule.Quotient.eq C).2 hm
    simpa [Submodule.mkQ_apply, hs q1, hs q2] using
      (show C.mkQ (s q1) = C.mkQ (s q2) from e)
  have himg : ∀ E : Submodule k H, ρ '' (E : Set H) = g '' ((Submodule.map C.mkQ E : Submodule k (H ⧸ C)) : Set (H ⧸ C)) := by
    intro E
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun a _ => hg a)
  have hcard : ∀ V : Submodule k (H ⧸ C), Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V
    have : Finite (H ⧸ C) := Module.finite_of_finite k
    letI := Fintype.ofFinite k
    letI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  refine ⟨?_, ?_⟩
  · rw [himg D, Nat.card_image_of_injective hinj]
    exact hcard _
  · intro D' hD
    rw [himg D, himg D', hD]

end UpperTheory.Gal.crystallineComparison.Mod
