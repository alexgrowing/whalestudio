import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem UpperTheory.Gal.crystallineComparison.one_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) :
    (1 : B) ∉ 𝔪 :=
  fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h)

private theorem UpperTheory.Gal.crystallineComparison.good_or {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) (e : B) :
    e ∉ 𝔪 ∨ 1 - e ∉ 𝔪 := by
  by_contra h
  push_neg at h
  exact one_not_mem h𝔪 (by simpa using 𝔪.add_mem h.1 h.2)

private theorem UpperTheory.Gal.crystallineComparison.mul_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    {a b : B} (ha : a ∉ 𝔪) (hb : b ∉ 𝔪) : a * b ∉ 𝔪 :=
  fun h => (h𝔪.mem_or_mem h).elim ha hb

private theorem UpperTheory.Gal.crystallineComparison.dvd_st {B : Type} [CommRing B] {a b e : B} (e' : B) (h : a ∣ e * b) :
    a ∣ e' * e * b := by
  rw [mul_assoc]
  exact Dvd.dvd.mul_left h e'

private theorem UpperTheory.Gal.crystallineComparison.good_combine {B ι : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    (s : Finset ι) (Q : ι → B → Prop) (st : ∀ i e e', Q i e → Q i (e' * e))
    (ex : ∀ i ∈ s, ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ Q i e) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ ∀ i ∈ s, Q i e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, by simp⟩
  | insert a s ha ih =>
    obtain ⟨e, he, hem, hQ⟩ := ih fun i hi => ex i (Finset.mem_insert_of_mem hi)
    obtain ⟨e', he', hem', hQ'⟩ := ex a (Finset.mem_insert_self a s)
    refine ⟨e' * e, he'.mul he, mul_not_mem h𝔪 hem' hem, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_comm]
      exact st _ _ _ hQ'
    · exact st _ _ _ (hQ i hi)

private theorem UpperTheory.Gal.crystallineComparison.power_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (d : B) (m : ℕ) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ (d ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * d) := by
  obtain ⟨e, he, h1, h2⟩ := hv d (ϖ ^ m) ⟨m, Ideal.subset_span (by simp)⟩
  rcases good_or h𝔪 e with g | g
  · exact ⟨e, he, g, Or.inr h1⟩
  · exact ⟨1 - e, he.one_sub, g, Or.inl h2⟩

private theorem UpperTheory.Gal.crystallineComparison.pair_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (M : ℕ) (d d' : B) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧
      ((∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M) → d ∣ e * d' ∨ d' ∣ e * d) := by
  by_cases h : ∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M
  · obtain ⟨e₀, h0, hm0, c, hc⟩ := h
    have h0' : e₀ * e₀ = e₀ := h0
    obtain ⟨f, hfd⟩ : ∃ f : B, f = e₀ * d + (1 - e₀) := ⟨_, rfl⟩
    have hf : e₀ * f = e₀ * d := by
      rw [hfd]
      linear_combination (d - 1) * h0'
    have hmem : ϖ ^ M ∈ Ideal.span {f, d'} := by
      have hP : ϖ ^ M = (e₀ * c + (1 - e₀) * ϖ ^ M) * f := by
        rw [hfd]
        linear_combination (-(c * d - c - d * ϖ ^ M + 2 * ϖ ^ M)) * h0' + e₀ * hc
      rw [hP]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    obtain ⟨e₁, h1, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hv f d' ⟨M, hmem⟩
    have A : d' ∣ (e₀ * e₁) * d := ⟨e₀ * a, by linear_combination e₀ * ha - e₁ * hf⟩
    have C : d ∣ (e₀ * (1 - e₁)) * d' := ⟨e₀ * b, by linear_combination e₀ * hb + b * hf⟩
    rcases good_or h𝔪 e₁ with g | g
    · exact ⟨e₀ * e₁, h0.mul h1, mul_not_mem h𝔪 hm0 g, fun _ => Or.inr A⟩
    · exact ⟨e₀ * (1 - e₁), h0.mul h1.one_sub, mul_not_mem h𝔪 hm0 g, fun _ => Or.inl C⟩
  · exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, fun h' => absurd h' h⟩

theorem UpperTheory.Gal.crystallineComparison.valLocal_of :
    ValLocal := by
  intro B _ ϖ hv 𝔪 h𝔪 D M
  obtain ⟨e₁, i₁, g₁, q₁⟩ := good_combine h𝔪 (D ×ˢ Finset.range (M + 1))
    (fun p e => p.1 ∣ e * ϖ ^ p.2 ∨ ϖ ^ p.2 ∣ e * p.1)
    (fun p e e' h => h.elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => power_good hv h𝔪 p.1 p.2)
  obtain ⟨e₂, i₂, g₂, q₂⟩ := good_combine h𝔪 (D ×ˢ D)
    (fun p e => (∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ p.1 ∣ e₀ * ϖ ^ M) →
      p.1 ∣ e * p.2 ∨ p.2 ∣ e * p.1)
    (fun p e e' h h' => (h h').elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => pair_good hv h𝔪 M p.1 p.2)
  refine ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, ?_, ?_⟩
  · intro d hd m hm
    have := q₁ (d, m) (Finset.mk_mem_product hd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
    exact this.elim (fun h => Or.inl (dvd_st e₂ h)) (fun h => Or.inr (dvd_st e₂ h))
  · intro d hd d' hd' hdv
    have := q₂ (d, d') (Finset.mk_mem_product hd hd') ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, hdv⟩
    rw [mul_comm e₂ e₁]
    exact this.elim (fun h => Or.inl (dvd_st e₁ h)) (fun h => Or.inr (dvd_st e₁ h))
