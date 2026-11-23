import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ConjPlace

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (j : K →+* ℂ_[q]) (y : 𝓞 K) :
    ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y); exact Subsingleton.elim _ _)

theorem norm_intCast_eq (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ = ‖((n : ℤ) : ℚ_[q])‖ := by
  have e : ((n : ℤ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℤ) : ℚ_[q]) := (map_intCast _ n).symm
  rw [e]
  exact PadicComplex.norm_extends' (p := q) _

theorem norm_intCast_lt_one_iff (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ < 1 ↔ (q : ℤ) ∣ n := by
  rw [norm_intCast_eq]
  exact Padic.norm_intCast_lt_one_iff

theorem exists_sq_add (q : ℕ) [Fact q.Prime] (d : ℕ) (h : jacobiSym (-(d : ℤ)) q = 1) :
    ¬ (q : ℤ) ∣ d ∧ ∃ t : ℤ, (q : ℤ) ∣ t ^ 2 + d := by
  have hl : legendreSym q (-(d : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff q _).2 h0] at hl
    exact zero_ne_one hl
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 hl
  refine ⟨?_, ⟨(r.val : ℤ), ?_⟩⟩
  · intro hd
    apply h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_neg.2 hd)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod q) * hr

theorem exists_small_not_conj {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E) (φ : E →+* ℂ) (c : E ≃ₐ[ℚ] E)
    (d q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hj : jacobiSym (-(d : ℤ)) q = 1) (ι : ℂ ≃+* ℂ_[q])
    (s : K) (hs : s * s = -(d : K)) (hc : c (algebraMap K E s) = -algebraMap K E s) :
    ∃ y : 𝓞 K, ‖ι (φ ((y : K) : E))‖ < 1 ∧ 1 ≤ ‖ι (φ (c ((y : K) : E)))‖ := by
  obtain ⟨hnd, t, ht⟩ := exists_sq_add q d hj
  have hint : IsIntegral ℤ s :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [sq, hs]⟩
  let B : 𝓞 K := ⟨s, hint⟩
  let j : E →+* ℂ_[q] := ι.toRingHom.comp φ
  let jK : K →+* ℂ_[q] := j.comp (algebraMap K E)
  have hc' : c (s : E) = -(s : E) := hc
  have hsE : (s : E) * (s : E) = -(d : E) := by
    have := congrArg (fun x : K => (x : E)) hs
    simpa using this
  have hcoe : ∀ u : ℤ, (((B + u : 𝓞 K) : K) : E) = (s : E) + (u : E) := by
    intro u; push_cast; rfl
  have hle : ∀ y : 𝓞 K, ‖j ((y : K) : E)‖ ≤ 1 := fun y => norm_le_one_of_int jK y

  have hodd : ∀ u : ℤ, (q : ℤ) ∣ 2 * u → (q : ℤ) ∣ u := by
    intro u h
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd h with h2 | h2
    · exfalso
      have : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    · exact h2
  have key : ∀ u : ℤ, (u = t ∨ u = -t) → ‖j (((B + u : 𝓞 K) : K) : E)‖ < 1 →
      1 ≤ ‖j (c (((B + u : 𝓞 K) : K) : E))‖ := by
    intro u hu h1
    by_contra h2
    push_neg at h2
    have e2 : c (((B + u : 𝓞 K) : K) : E) = -(s : E) + (u : E) := by
      rw [hcoe, map_add, map_intCast, hc']
    have hsum : j (((B + u : 𝓞 K) : K) : E) + j (c (((B + u : 𝓞 K) : K) : E)) = (((2 * u : ℤ)) : ℂ_[q]) := by
      rw [e2, hcoe, ← map_add]
      have : (s : E) + (u : E) + (-(s : E) + (u : E)) = ((2 * u : ℤ) : E) := by push_cast; ring
      rw [this, map_intCast]
    have hlt : ‖(((2 * u : ℤ)) : ℂ_[q])‖ < 1 := by
      rw [← hsum]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
    have hdu : (q : ℤ) ∣ u := hodd u ((norm_intCast_lt_one_iff q _).1 hlt)
    have hdt : (q : ℤ) ∣ t := by
      rcases hu with rfl | rfl
      · exact hdu
      · exact dvd_neg.1 hdu
    exact hnd ((dvd_add_right (dvd_pow hdt two_ne_zero)).1 ht)
  have hprod : j (((B + t : 𝓞 K) : K) : E) * j (((B + (-t : ℤ) : 𝓞 K) : K) : E) = ((-(t ^ 2 + d) : ℤ) : ℂ_[q]) := by
    rw [← map_mul, hcoe, hcoe]
    have : ((s : E) + (t : E)) * ((s : E) + ((-t : ℤ) : E)) = ((-(t ^ 2 + d) : ℤ) : E) := by
      push_cast
      linear_combination hsE
    rw [this, map_intCast]
  have hpl : ‖((-(t ^ 2 + d) : ℤ) : ℂ_[q])‖ < 1 := (norm_intCast_lt_one_iff q _).2 (dvd_neg.2 ht)
  by_cases h1 : ‖j (((B + t : 𝓞 K) : K) : E)‖ < 1
  · exact ⟨B + t, h1, key t (Or.inl rfl) h1⟩
  · push_neg at h1
    have h2 : ‖j (((B + (-t : ℤ) : 𝓞 K) : K) : E)‖ < 1 := by
      by_contra h2
      push_neg at h2
      rw [← hprod, norm_mul] at hpl
      nlinarith
    exact ⟨B + (-t : ℤ), h2, key (-t) (Or.inr rfl) h2⟩

theorem conj_place_ne : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 →
    ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧
      1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  intro D q _ hq2 hj ι
  obtain ⟨s, h1, h2⟩ := sqrtInK D
  exact exists_small_not_conj D.host.K D.host.φ₀ D.host.conj D.host.d q hq2 hj ι s h1 h2

end GlobalTheory.ConjPlace
