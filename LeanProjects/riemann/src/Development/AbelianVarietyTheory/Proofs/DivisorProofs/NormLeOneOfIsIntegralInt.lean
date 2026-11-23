import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongWtLvLac

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CongW.PlaceEmb

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_isIntegral_int {x : PadicAlgCl p} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl p)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl p))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_int_le (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : ‖σ (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int σ (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (σ : K →+* PadicAlgCl p) : Ideal (𝓞 K) where
  carrier := {y | ‖σ (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : σ ((a + b : 𝓞 K) : K) = σ (a : K) + σ (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : σ ((c • a : 𝓞 K) : K) = σ (c : K) * σ (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le σ c
    nlinarith [norm_nonneg (σ (c : K)), norm_nonneg (σ (a : K))]

theorem mem_smallIdeal (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : y ∈ smallIdeal σ ↔ ‖σ (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (σ : K →+* PadicAlgCl p) : (smallIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : σ ((a * b : 𝓞 K) : K) = σ (a : K) * σ (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h : ‖algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := norm_algebraMap' _ _
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h, map_natCast] at h2
  exact h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* PadicAlgCl p, w.asIdeal = smallIdeal σ := by
  by_contra hcon
  push_neg at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, ¬ w.asIdeal ≤ smallIdeal (σ : K →+* PadicAlgCl p) := by
    intro σ hle
    exact hcon (σ : K →+* PadicAlgCl p) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] PadicAlgCl p)) : Set (K →ₐ[ℚ] PadicAlgCl p)),
        (smallIdeal (σ : K →+* PadicAlgCl p) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = ∏ σ : K →ₐ[ℚ] PadicAlgCl p, σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : PadicAlgCl p)‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = (p : PadicAlgCl p) * ((m : ℤ) : PadicAlgCl p) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : PadicAlgCl p)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : PadicAlgCl p), norm_nonneg ((m : ℤ) : PadicAlgCl p)]

end GlobalTheory.CongW.PlaceEmb

namespace GlobalTheory.CongW

open Formalism.ConjugateSelfDual

end GlobalTheory.CongW
