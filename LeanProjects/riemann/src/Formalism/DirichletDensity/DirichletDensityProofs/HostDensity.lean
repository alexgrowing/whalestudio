import Mathlib
import Formalism.DirichletDensity.Statement
import Formalism.CMTypeGalois.HalfTypesFromGeneral

open NumberField Ideal Filter Topology Formalism.Q3

noncomputable section

namespace Formalism.HF.P

theorem dirDensity_congr {S T : Set ℕ} {δ : ℝ} (h : DirDensity S δ)
    (hST : ∀ p : ℕ, p.Prime → (p ∈ S ↔ p ∈ T)) : DirDensity T δ := by
  have hset : {p : ℕ | p.Prime ∧ p ∈ S} = {p : ℕ | p.Prime ∧ p ∈ T} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨hp, hs⟩ => ⟨hp, (hST p hp).1 hs⟩, fun ⟨hp, ht⟩ => ⟨hp, (hST p hp).2 ht⟩⟩
  unfold DirDensity at h ⊢
  rw [← hset]
  exact h

theorem span_maximal (p : ℕ) (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by
  have hprime : (span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hne : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  exact hprime.isMaximal hne

theorem frob_iff_chi (q : Fin 3 → ℕ) (hq : Hyp3 q) (E : Type) [Field E] [NumberField E]
    (α : Fin 3 → E) (hE : IsHost q α) (g : Gal3) (p : ℕ) (hp : p.Prime)
    (hpq : ∀ i, p ≠ q i) :
    (∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ)),
        IsArithFrobAt ℤ σ P → galSign α σ = g) ↔
      ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro H i
    have := span_maximal p hp
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
    have : P.IsPrime := hPm.isPrime
    have := hPl
    obtain ⟨σ, hσ⟩ := (hostFrob q hq E α hE p hpq P).1
    have h1 := H P σ hσ
    have h2 := ((hostFrob q hq E α hE p hpq P).2 σ).1 hσ i
    rw [← h2, h1]
  · intro H P _ _ σ hσ
    have h2 := ((hostFrob q hq E α hE p hpq P).2 σ).1 hσ
    funext i
    exact Units.ext ((h2 i).trans (H i))

end Formalism.HF.P

namespace Formalism.HF

theorem hostDensity_of (hA : HostDensityArith) : HostDensity := by
  intro q hq E _ _ α hE g
  refine P.dirDensity_congr (hA q hq g).2 ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpq, hchi⟩
    exact ⟨hpq, (P.frob_iff_chi q hq E α hE g p hp hpq).2 hchi⟩
  · rintro ⟨hpq, hfrob⟩
    exact ⟨hpq, (P.frob_iff_chi q hq E α hE g p hp hpq).1 hfrob⟩

end Formalism.HF
