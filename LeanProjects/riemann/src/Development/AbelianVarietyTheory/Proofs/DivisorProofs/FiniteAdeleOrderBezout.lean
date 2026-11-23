import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace GlobalTheory.AdeleRing

theorem bezout_units_idempotent : ∀ (E : Type) [Field E] [NumberField E] (R : Set (FiniteAdeleRing (𝓞 E) E)), (∀ y, y ∈ R ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (y P) ≤ 1) →
    (∀ a b : FiniteAdeleRing (𝓞 E) E, ∃ u ∈ R, ∃ v ∈ R, ∃ r ∈ R, ∃ r' ∈ R, a = r * (u * a + v * b) ∧ b = r' * (u * a + v * b)) ∧
    (∀ p ∈ R, ∀ q ∈ R, ∃ s ∈ R, ∃ t ∈ R, ∃ d ∈ R, ∃ d' ∈ R, (s + t * p) * d = 1 ∧ (s * q + t) * d' = 1) ∧
    (∀ c ∈ R, ∃ e ∈ R, ∃ d ∈ R, e * e = e ∧ e * c * d = e ∧ ∀ m ∈ R, ∀ m' ∈ R, m * m' = 1 → ∀ a ∈ R, ∃ d' ∈ R, (m + (1 - e) * c * a) * d' = 1) := by
  intro E _ _ R hR
  classical
  have mk : ∀ f : ∀ P : HeightOneSpectrum (𝓞 E), P.adicCompletion E, (∀ P, Valued.v (f P) ≤ 1) →
      ∃ y ∈ R, ∀ P, y P = f P := by
    intro f hf
    refine ⟨⟨f, Filter.Eventually.of_forall fun P =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E P).2 (hf P)⟩, (hR _).2 (fun P => hf P), fun P => rfl⟩
  have hmul : ∀ (x y : FiniteAdeleRing (𝓞 E) E) P, (x * y) P = x P * y P := fun _ _ _ => rfl
  have hadd : ∀ (x y : FiniteAdeleRing (𝓞 E) E) P, (x + y) P = x P + y P := fun _ _ _ => rfl
  have hsub : ∀ (x y : FiniteAdeleRing (𝓞 E) E) P, (x - y) P = x P - y P := fun _ _ _ => rfl
  have hone : ∀ P, (1 : FiniteAdeleRing (𝓞 E) E) P = 1 := fun _ => rfl
  have hv0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E), Valued.v x = 0 → x = 0 := fun P x h => (Valued.v).zero_iff.1 h
  have hinv : ∀ (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E), Valued.v x = 1 → Valued.v x⁻¹ ≤ 1 := fun P x h => by
    rw [map_inv₀, h, inv_one]
  have hne : ∀ (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E), Valued.v x = 1 → x ≠ 0 := fun P x h h0 => by
    rw [h0, map_zero] at h; exact zero_ne_one h
  refine ⟨fun a b => ?_, fun p hp q hq => ?_, fun c hc => ?_⟩
  · obtain ⟨u, hu, hu'⟩ := mk (fun P => if Valued.v (b P) ≤ Valued.v (a P) then 1 else 0)
      (fun P => by split_ifs <;> simp)
    obtain ⟨w, hw, hw'⟩ := mk (fun P => if Valued.v (b P) ≤ Valued.v (a P) then 0 else 1)
      (fun P => by split_ifs <;> simp)
    obtain ⟨r, hr, hr'⟩ := mk (fun P => if Valued.v (b P) ≤ Valued.v (a P) then 1 else a P / b P)
      (fun P => by
        split_ifs with h
        · simp
        · rw [not_le] at h
          rw [map_div₀, div_le_one₀ (lt_of_le_of_lt zero_le' h)]
          exact h.le)
    obtain ⟨r', hr'', hr'''⟩ := mk (fun P => if Valued.v (b P) ≤ Valued.v (a P) then b P / a P else 1)
      (fun P => by
        split_ifs with h
        · by_cases h0 : Valued.v (a P) = 0
          · rw [hv0 P _ h0, div_zero, map_zero]; exact zero_le'
          · rw [map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm h0))]
            exact h
        · simp)
    refine ⟨u, hu, w, hw, r, hr, r', hr'', ?_, ?_⟩
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hadd, hmul, hmul, hu', hw', hr']
      split_ifs with h
      · simp
      · rw [not_le] at h
        have hb : b P ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact not_lt_zero' h
        rw [zero_mul, one_mul, zero_add, div_mul_cancel₀ _ hb]
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hadd, hmul, hmul, hu', hw', hr''']
      split_ifs with h
      · by_cases h0 : a P = 0
        · have : Valued.v (b P) = 0 := le_antisymm (by rw [h0, map_zero] at h; exact h) zero_le'
          rw [hv0 P _ this, h0]; simp
        · rw [one_mul, zero_mul, add_zero, div_mul_cancel₀ _ h0]
      · simp
  · have hpP : ∀ P, Valued.v (p P) ≤ 1 := (hR p).1 hp
    have hqP : ∀ P, Valued.v (q P) ≤ 1 := (hR q).1 hq
    let sf : ∀ P : HeightOneSpectrum (𝓞 E), P.adicCompletion E := fun P => if Valued.v (p P) = 1 then 0 else 1
    let tf : ∀ P : HeightOneSpectrum (𝓞 E), P.adicCompletion E := fun P =>
      if Valued.v (p P) = 1 then 1 else if Valued.v (q P) = 1 then 0 else 1
    have h1 : ∀ P, Valued.v (sf P + tf P * p P) = 1 := fun P => by
      simp only [sf, tf]
      split_ifs with h h'
      · simpa using h
      · simp
      · rw [one_mul, Valuation.map_one_add_of_lt]
        exact lt_of_le_of_ne (hpP P) h
    have h2 : ∀ P, Valued.v (sf P * q P + tf P) = 1 := fun P => by
      simp only [sf, tf]
      split_ifs with h h'
      · simp
      · simpa using h'
      · rw [one_mul, add_comm, Valuation.map_one_add_of_lt]
        exact lt_of_le_of_ne (hqP P) h'
    obtain ⟨s, hs, hs'⟩ := mk sf (fun P => by simp only [sf]; split_ifs <;> simp)
    obtain ⟨t, ht, ht'⟩ := mk tf (fun P => by simp only [tf]; split_ifs <;> simp)
    obtain ⟨d, hd, hd'⟩ := mk (fun P => (sf P + tf P * p P)⁻¹) (fun P => hinv P _ (h1 P))
    obtain ⟨d', hd'', hd'''⟩ := mk (fun P => (sf P * q P + tf P)⁻¹) (fun P => hinv P _ (h2 P))
    refine ⟨s, hs, t, ht, d, hd, d', hd'', ?_, ?_⟩
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hadd, hmul, hs', ht', hd', hone]
      exact mul_inv_cancel₀ (hne P _ (h1 P))
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hadd, hmul, hs', ht', hd''', hone]
      exact mul_inv_cancel₀ (hne P _ (h2 P))
  · have hcP : ∀ P, Valued.v (c P) ≤ 1 := (hR c).1 hc
    obtain ⟨e, he, he'⟩ := mk (fun P => if Valued.v (c P) = 1 then 1 else 0)
      (fun P => by split_ifs <;> simp)
    obtain ⟨d, hd, hd'⟩ := mk (fun P => if Valued.v (c P) = 1 then (c P)⁻¹ else 0)
      (fun P => by
        split_ifs with h
        · exact hinv P _ h
        · simp)
    refine ⟨e, he, d, hd, ?_, ?_, ?_⟩
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, he']
      split_ifs <;> simp
    · refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hmul, he', hd']
      split_ifs with h
      · rw [one_mul, mul_inv_cancel₀ (hne P _ h)]
      · simp
    · intro m hm m' hm' hmm a ha
      have hmP : ∀ P, Valued.v (m P) = 1 := fun P => by
        have h1 : Valued.v (m P) * Valued.v (m' P) = 1 := by
          rw [← map_mul, ← hmul, hmm, hone, map_one]
        refine le_antisymm ((hR m).1 hm P) ?_
        calc (1 : _) = Valued.v (m P) * Valued.v (m' P) := h1.symm
          _ ≤ Valued.v (m P) := mul_le_of_le_one_right' ((hR m').1 hm' P)
      have hX : ∀ P, Valued.v (m P + (1 - e P) * c P * a P) = 1 := fun P => by
        rw [he']
        split_ifs with h
        · rw [sub_self, zero_mul, zero_mul, add_zero, hmP P]
        · rw [Valuation.map_add_eq_of_lt_left, hmP P]
          rw [hmP P, sub_zero, one_mul, map_mul]
          calc Valued.v (c P) * Valued.v (a P) ≤ Valued.v (c P) := mul_le_of_le_one_right' ((hR a).1 ha P)
            _ < 1 := lt_of_le_of_ne (hcP P) h
      obtain ⟨d', hd'', hd'''⟩ := mk (fun P => (m P + (1 - e P) * c P * a P)⁻¹) (fun P => hinv P _ (hX P))
      refine ⟨d', hd'', ?_⟩
      refine IsDedekindDomain.FiniteAdeleRing.ext E fun P => ?_
      rw [hmul, hadd, hmul, hmul, hsub, hone, hd''']
      exact mul_inv_cancel₀ (hne P _ (hX P))

end GlobalTheory.AdeleRing
