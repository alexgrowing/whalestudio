import Mathlib
import Formalism.LocalRingCardinality.DataLatDefs

namespace GlobalTheory.EX.Glue

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_clear {R : Type} [CommRing R] [IsDedekindDomain R] (c : R) (hc : c ≠ 0)
    (w₀ : HeightOneSpectrum R) :
    ∃ t : R, t ∉ w₀.asIdeal ∧ ∀ w : HeightOneSpectrum R, w ≠ w₀ → ∃ s : R, s ∉ w.asIdeal ∧ c ∣ s * t := by
  classical
  haveI := w₀.isMaximal
  have hI : Ideal.span {c} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI w₀.asIdeal
  have hQn : ¬ Q ≤ w₀.asIdeal := by
    intro h
    rw [sup_eq_left.2 h] at hQ
    exact w₀.isPrime.ne_top hQ
  obtain ⟨t, htQ, ht⟩ := SetLike.not_le_iff_exists.1 hQn
  refine ⟨t, ht, fun w hw => ?_⟩
  generalize Multiset.count w₀.asIdeal _ = k at hfac
  have hP : ¬ w₀.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    haveI := w.isPrime
    have h' : w₀.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hw (HeightOneSpectrum.ext (w₀.isMaximal.eq_of_le w.isPrime.ne_top h').symm)
  obtain ⟨s, hsP, hs⟩ := SetLike.not_le_iff_exists.1 hP
  refine ⟨s, hs, ?_⟩
  rw [← Ideal.mem_span_singleton, hfac]
  exact Ideal.mul_mem_mul hsP htQ

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

def locSub (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w M x}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  smul_mem' := by
    rintro a x ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hx⟩

theorem mem_locSub {w : HeightOneSpectrum (𝓞 K)} {M : Submodule (𝓞 K) V} {x : V} :
    x ∈ locSub w M ↔ InLoc w M x := Iff.rfl

theorem inLoc_iInf (B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V)
    (hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w)
    (hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w) (w₀ : HeightOneSpectrum (𝓞 K)) (x : V) :
    InLoc w₀ (⨅ w, B w) x ↔ x ∈ B w₀ := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w₀ s x hs ((Submodule.mem_iInf _).1 hx w₀)
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hden x
    obtain ⟨t, ht, h⟩ := exists_clear c hc w₀
    refine ⟨t, ht, (Submodule.mem_iInf _).2 fun w => ?_⟩
    by_cases hw : w = w₀
    · subst hw; exact (B w).smul_mem _ hx
    · obtain ⟨s, hs, d, hd⟩ := h w hw
      refine hsat w s _ hs ?_
      rw [← mul_smul, hd, mul_comm, mul_smul]
      exact (B w).smul_mem _ (hcx w)

theorem exists_glue : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (A : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V), S.Finite →
    (∀ x : V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ M) →
    (∀ w ∈ S, (∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A w → x ∈ A w) ∧
      ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ M, n • x ∈ A w) ∧ ∀ x ∈ A w, InLoc w M (n • x)) →
    ∃ N : Submodule (𝓞 K) V, (∀ w ∈ S, ∀ x, InLoc w N x ↔ x ∈ A w) ∧
      ∀ w ∉ S, ∀ x, InLoc w N x ↔ InLoc w M x := by
  intro K V _ _ _ _ _ _ M S A hS hM hA
  classical
  let B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V := fun w => if w ∈ S then A w else locSub w M
  have hB1 : ∀ w ∈ S, B w = A w := fun w hw => if_pos hw
  have hB2 : ∀ w ∉ S, B w = locSub w M := fun w hw => if_neg hw
  have hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w := by
    intro w t x ht hx
    by_cases hw : w ∈ S
    · rw [hB1 w hw] at hx ⊢
      exact (hA w hw).1 t x ht hx
    · rw [hB2 w hw] at hx ⊢
      obtain ⟨s, hs, hx⟩ := hx
      exact ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, by rwa [mul_smul]⟩
  have hn : ∀ w, ∃ n : ℕ, n ≠ 0 ∧ (w ∈ S → ∀ x ∈ M, n • x ∈ A w) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n, hn, h, -⟩ := (hA w hw).2
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose n hn0 hn using hn
  have hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w := by
    intro x
    obtain ⟨m, hm, hx⟩ := hM x
    refine ⟨(((∏ w ∈ hS.toFinset, n w) * m : ℕ) : 𝓞 K), ?_, fun w => ?_⟩
    · exact Nat.cast_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hn0 w) hm)
    · rw [Nat.cast_smul_eq_nsmul, mul_smul]
      by_cases hw : w ∈ S
      · rw [hB1 w hw]
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem n (hS.mem_toFinset.2 hw)
        rw [hd, mul_comm, mul_smul]
        exact nsmul_mem (hn w hw _ hx) d
      · rw [hB2 w hw]
        exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by
          rw [one_smul]; exact nsmul_mem hx _⟩
  refine ⟨⨅ w, B w, fun w hw x => ?_, fun w hw x => ?_⟩
  · rw [inLoc_iInf B hsat hden, hB1 w hw]
  · rw [inLoc_iInf B hsat hden, hB2 w hw, mem_locSub]

end GlobalTheory.EX.Glue
