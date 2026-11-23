import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.isDPMorphism_of_isStd :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)),
      Q.IsStd δ η → ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (F : Q.P →+* C) (c : C),
        c ∈ J'' → IsDPMorphism δ δ'' (F.comp (algebraMap B Q.P)) → (∀ n, F (Q.e n) = δ''.dpow n c) →
          IsDPMorphism η δ'' F := by
  intro B _ J δ Q η hQ C _ J'' δ'' F c hc hF he
  have hS : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
    rw [Ideal.span_union, ← Ideal.map_span, Ideal.span_eq]; rfl
  refine IsDPMorphism.on_span η δ'' hS ?_ ?_
  · rintro s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · exact hF.1 (Ideal.mem_map_of_mem _ ha)
    · rw [he]; exact δ''.dpow_mem k.succ_ne_zero hc
  · rintro n s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · rw [hQ.dp.2 a ha]
      exact (hF.2 a ha).symm
    · have h1 := Q.e_one_mem_ext J
      show F (η.dpow n (Q.e (k + 1))) = δ''.dpow n (F (Q.e (k + 1)))
      have h2 : η.dpow n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
        rw [← hQ.var (k + 1), η.dpow_comp k.succ_ne_zero h1, hQ.var]
      rw [h2, map_mul, map_natCast, he, he, δ''.dpow_comp k.succ_ne_zero hc]

end GlobalTheory.PDA
