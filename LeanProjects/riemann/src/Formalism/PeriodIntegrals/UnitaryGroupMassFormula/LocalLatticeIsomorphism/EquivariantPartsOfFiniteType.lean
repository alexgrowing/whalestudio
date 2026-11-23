import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

section conj
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]

def conjK (cj : E ≃ₐ[ℚ] E) (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') :
    K →+* K where
  toFun k := Classical.choose (h k)
  map_one' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 1)) = algebraMap K E 1
    rw [← Classical.choose_spec (h 1)]; simp
  map_mul' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x * y))) =
      algebraMap K E (Classical.choose (h x) * Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x * y), map_mul (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_mul, map_mul]
  map_zero' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 0)) = algebraMap K E 0
    rw [← Classical.choose_spec (h 0)]; simp
  map_add' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x + y))) =
      algebraMap K E (Classical.choose (h x) + Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x + y), map_add (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_add, map_add]

theorem conjK_spec (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') (k : K) :
    algebraMap K E (conjK cj h k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (h k)).symm

theorem sum_conj (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {ι : Type} [Fintype ι]
    (v w : ι → K) :
    ∑ i, algebraMap K E (v i) * cj (algebraMap K E (w i)) = algebraMap K E (hf (conjK cj h) v w) := by
  simp only [hf, map_sum, map_mul, conjK_spec]

theorem trace_natCast_mul (cj : E ≃ₐ[ℚ] E) (s t : ℕ) (x y : E) :
    Algebra.trace K E (((s : E) * x) * cj ((t : E) * y)) =
      ((s * t : ℕ) : K) * Algebra.trace K E (x * cj y) := by
  have e : ((s : E) * x) * cj ((t : E) * y) = algebraMap K E ((s * t : ℕ) : K) * (x * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; push_cast; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]

end conj

section rp
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem Rp_finset {α : Type} (T : Finset α) (f : α → K) (h : ∀ z ∈ T, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z ∈ T, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | insert a T ha ih =>
    obtain ⟨s, hs, hsT⟩ := ih fun z hz => h z (Finset.mem_insert_of_mem hz)
    obtain ⟨t, ht, hta⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have e : ((s * t : ℕ) : K) * f z = (s : K) * ((t : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ s) hta
    · have e : ((s * t : ℕ) : K) * f z = (t : K) * ((s : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ t) (hsT z hz)

theorem Rp_fintype {α : Type} [Fintype α] (f : α → K) (h : ∀ z, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, h'⟩ := Rp_finset (p := p) Finset.univ f fun z _ => h z
  exact ⟨s, hs, fun z => h' z (Finset.mem_univ z)⟩

end rp

section main
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem conjK_invol (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) (k : K) :
    conjK cj hc.2.1 (conjK cj hc.2.1 k) = k :=
  (algebraMap K E).injective (by rw [conjK_spec, conjK_spec, hc.1])

theorem splitK_of (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {p : ℕ}
    (hs : PI.KerIso.SplitsAt K cj p) : SplitK (conjK cj hc.2.1) p := by
  obtain ⟨P, hP, hpP, a, b, hab, ha, hb⟩ := hs
  exact ⟨P, hP, hpP, a, b, (algebraMap K E).injective (by rw [conjK_spec, hab]), ha, hb⟩

theorem hf_isom (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {n : Type} [Fintype n]
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (hg : PI.KerIso.IsIsom cj g₀) (x y : Fin 4 → E) :
    hf (conjK cj h) (g₀ x) (g₀ y) = ∑ a, Algebra.trace K E (x a * cj (y a)) :=
  (algebraMap K E).injective (by rw [← sum_conj, hg])

def Lset {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Set (Fin 4 × n → K) :=
  {v | ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g₀.symm v a ∈ I}

end main

end PI.KLW
