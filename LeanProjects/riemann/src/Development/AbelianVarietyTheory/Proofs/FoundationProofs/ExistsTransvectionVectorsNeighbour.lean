import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeTo

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NbVec

section Scalar

variable {K : Type} [Field K] [NumberField K]

theorem int_of_mul {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {θ : K}
    (h : ∀ p ∈ P, (p : K) * θ ∈ (algebraMap (𝓞 K) K).range) {r : 𝓞 K} (hr : r ∉ P)
    (hrθ : (r : K) * θ ∈ (algebraMap (𝓞 K) K).range) : θ ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨u, p, hp, e⟩ := hP.exists_inv hr
  have e' : (u : K) * r + p = 1 := by
    have := congrArg (algebraMap (𝓞 K) K) e
    simpa using this
  have : θ = (u : K) * ((r : K) * θ) + (p : K) * θ := by linear_combination (-θ) * e'
  rw [this]
  exact add_mem (mul_mem ⟨u, rfl⟩ hrθ) (h p hp)

theorem exists_mul_notMem {P : Ideal (𝓞 K)} (hP0 : P ≠ ⊥) {θ : K}
    (h : ∀ p ∈ P, (p : K) * θ ∈ (algebraMap (𝓞 K) K).range) (hθ : θ ∉ (algebraMap (𝓞 K) K).range) :
    ∃ p ∈ P, ∃ a : 𝓞 K, a ∉ P ∧ (a : K) = (p : K) * θ := by
  by_contra hcon
  push_neg at hcon
  apply hθ
  have hint : IsIntegral (𝓞 K) θ := by
    refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap (𝓞 K) K) P) ?_
      ((IsNoetherian.noetherian P).map _) θ ?_
    · intro hb
      apply hP0
      rw [eq_bot_iff]
      intro p hp
      have : algebraMap (𝓞 K) K p ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) P := ⟨p, hp, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact (FaithfulSMul.algebraMap_injective (𝓞 K) K) (this.trans (map_zero _).symm)
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨a, ha⟩ := h p hp
      have haP : a ∈ P := by
        by_contra hn
        exact hcon p hp a hn ha
      exact ⟨a, haP, by rw [smul_eq_mul, mul_comm]; exact ha⟩
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hint

theorem exists_sub_mul {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hP0 : P ≠ ⊥) {θ η : K}
    (h : ∀ p ∈ P, (p : K) * θ ∈ (algebraMap (𝓞 K) K).range) (hθ : θ ∉ (algebraMap (𝓞 K) K).range)
    (hη : ∀ p ∈ P, (p : K) * η ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : 𝓞 K, η - (u : K) * θ ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨p, hp, a, ha, e⟩ := exists_mul_notMem hP0 h hθ
  obtain ⟨v, p₀, hp₀, e₁⟩ := hP.exists_inv ha
  have e' : (v : K) * a + p₀ = 1 := by
    have := congrArg (algebraMap (𝓞 K) K) e₁
    simpa using this
  obtain ⟨t, ht⟩ := hη p hp
  refine ⟨v * t, ?_⟩
  have ht' : (t : K) = (p : K) * η := ht
  have : η - ((v * t : 𝓞 K) : K) * θ = (p₀ : K) * η := by
    have e2 : ((v * t : 𝓞 K) : K) = (v : K) * t := rfl
    rw [e2, ht']
    linear_combination (-η) * e' + (v : K) * η * e
  rw [this]
  exact hη p₀ hp₀

theorem exists_c {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : 𝓞 K} (hq : q ≠ 0) :
    ∃ c : 𝓞 K, c ∉ P ∧ ∀ Q : Ideal (𝓞 K), Q.IsPrime → q ∈ Q → Q ≠ P → c ∈ Q := by
  haveI := hP
  obtain ⟨J, hJ, e⟩ := Ideal.eq_prime_pow_mul_coprime
    (I := Ideal.span {q}) (by simpa using hq) P
  have : (1 : 𝓞 K) ∈ P ⊔ J := by rw [hJ]; trivial
  obtain ⟨p, hp, c, hc, e₁⟩ := Submodule.mem_sup.1 this
  refine ⟨c, fun hcP => hP.ne_top ((Ideal.eq_top_iff_one _).2 (e₁ ▸ P.add_mem hp hcP)), fun Q hQ hqQ hne => ?_⟩
  have hle : Ideal.span {q} ≤ Q := (Ideal.span_singleton_le_iff_mem _).2 hqQ
  rw [e] at hle
  rcases hQ.mul_le.1 hle with h | h
  · exact absurd (hP.eq_of_le hQ.ne_top (Ideal.IsPrime.le_of_pow_le h)).symm hne
  · exact h hc

theorem exists_nat {q : ℕ} (hq : q.Prime) (μ : K)
    (h : ∀ Q : Ideal (𝓞 K), Q.IsPrime → (q : 𝓞 K) ∈ Q → ∃ p a : 𝓞 K, a ∉ Q ∧ (a : K) = (p : K) * μ) :
    ∃ m : ℕ, Nat.Coprime m q ∧ ∃ r : 𝓞 K, (m : K) = (r : K) * μ := by
  let J : Ideal (𝓞 K) :=
    { carrier := {a | ∃ r : 𝓞 K, (a : K) = (r : K) * μ}
      add_mem' := by
        rintro a b ⟨r, hr⟩ ⟨s, hs⟩
        exact ⟨r + s, by
          show (a : K) + b = ((r : K) + s) * μ
          rw [hr, hs, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨r, hr⟩
        exact ⟨c * r, by
          show (c : K) * a = ((c : K) * r) * μ
          rw [hr, mul_assoc]⟩ }
  haveI hqp : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq)
  have hnot : ¬ J.comap (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(q : ℤ)} := by
    intro hle
    obtain ⟨Q, hJQ, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(q : ℤ)}) J hle
    have hqQ : (q : 𝓞 K) ∈ Q := by
      have : (q : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by rw [hc]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.mem_comap] using this
    obtain ⟨p, a, ha, e⟩ := h Q hQ hqQ
    exact ha (hJQ ⟨p, e⟩)
  obtain ⟨z, hz, hzq⟩ := Set.not_subset.1 hnot
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, ((algebraMap ℤ (𝓞 K) z : 𝓞 K) : K) = (r : K) * μ := hz
  have hr' : (z : K) = (r : K) * μ := by simpa using hr
  refine ⟨z.natAbs, ?_, ?_⟩
  · refine ((Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hzq ?_).symm
    exact Ideal.mem_span_singleton.2 (Int.natCast_dvd.2 hd)
  · rcases Int.natAbs_eq z with e | e
    · exact ⟨r, by rw [← hr', ← Int.cast_natCast, ← e]⟩
    · refine ⟨-r, ?_⟩
      have : ((z.natAbs : ℕ) : K) = -(z : K) := by
        rw [← Int.cast_natCast, ← Int.cast_neg]; congr 1; omega
      rw [this, hr']
      show _ = (-(r : K)) * μ
      ring

end Scalar

theorem IntE.add {D : D7} {a b : D.host.E} (ha : IntE D a) (hb : IntE D b) : IntE D (a + b) := add_mem ha hb
theorem IntE.sub {D : D7} {a b : D.host.E} (ha : IntE D a) (hb : IntE D b) : IntE D (a - b) := sub_mem ha hb
theorem IntE.mul {D : D7} {a b : D.host.E} (ha : IntE D a) (hb : IntE D b) : IntE D (a * b) := mul_mem ha hb
theorem intE_coe (D : D7) (a : 𝓞 D.host.E) : IntE D (a : D.host.E) := ⟨a, rfl⟩

theorem conj_notMem {D : D7} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {c : 𝓞 D.host.E} (hc : c ∉ P) :
    sgO D c ∉ P := fun h => hc (by simpa only [sgO_sgO] using hσ _ h)

theorem intE_mul_conj {D : D7} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {θ : D.host.E}
    (h : ∀ p ∈ P, IntE D ((p : D.host.E) * θ)) : ∀ p ∈ P, IntE D ((p : D.host.E) * D.host.conj θ) := by
  intro p hp
  have := (h _ (hσ p hp)).conj
  rwa [map_mul, sgO_coe, conj_conj] at this

theorem exists_u {D : D7} {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hP0 : P ≠ ⊥) (hσ : ∀ a ∈ P, sgO D a ∈ P)
    {w : 𝓞 D.host.E} (hw : w - sgO D w ∉ P) {θ : D.host.E}
    (h : ∀ p ∈ P, IntE D ((p : D.host.E) * θ)) (hθ : ¬ IntE D θ) :
    ∃ u : 𝓞 D.host.E, ¬ IntE D ((u : D.host.E) * θ) ∧
      IntE D ((u : D.host.E) * θ + D.host.conj ((u : D.host.E) * θ)) := by
  have key : ∀ v : 𝓞 D.host.E, ¬ IntE D ((v : D.host.E) * θ - D.host.conj ((v : D.host.E) * θ)) →
      ∃ u : 𝓞 D.host.E, ¬ IntE D ((u : D.host.E) * θ) ∧
        IntE D ((u : D.host.E) * θ + D.host.conj ((u : D.host.E) * θ)) := by
    intro v hv
    have hv1 : ∀ p ∈ P, IntE D ((p : D.host.E) * ((v : D.host.E) * θ)) := fun p hp => by
      rw [mul_left_comm]; exact IntE.mul (intE_coe D v) (h p hp)
    have hη : ∀ p ∈ P, IntE D ((p : D.host.E) * ((v : D.host.E) * θ - D.host.conj ((v : D.host.E) * θ))) :=
      fun p hp => by rw [mul_sub]; exact IntE.sub (hv1 p hp) (intE_mul_conj hσ hv1 p hp)
    obtain ⟨u, hu⟩ := exists_sub_mul hP hP0 h hθ hη
    have hu' : IntE D ((v : D.host.E) * θ - D.host.conj ((v : D.host.E) * θ) - (u : D.host.E) * θ) := hu
    refine ⟨u, fun hi => hv ?_, ?_⟩
    · have := IntE.add hu' hi
      rwa [sub_add_cancel] at this
    · have h2 := hu'.conj
      rw [map_sub, map_sub, conj_conj] at h2
      have h3 := IntE.sub (IntE.sub (intE_coe D 0) hu') h2
      have h0 : ((0 : 𝓞 D.host.E) : D.host.E) = 0 := rfl
      convert h3 using 1
      rw [h0]; ring
  by_cases h1 : IntE D (((1 : 𝓞 D.host.E) : D.host.E) * θ - D.host.conj (((1 : 𝓞 D.host.E) : D.host.E) * θ))
  · refine key w fun h2 => hθ ?_
    have h1' : ((1 : 𝓞 D.host.E) : D.host.E) = 1 := rfl
    rw [h1', one_mul] at h1
    refine int_of_mul hP h hw ?_
    have h3 := IntE.sub h2 (IntE.mul (intE_coe D (sgO D w)) h1)
    have e : ((w - sgO D w : 𝓞 D.host.E) : D.host.E) = (w : D.host.E) - D.host.conj w := rfl
    rw [e]
    rw [map_mul, sgO_coe] at h3
    show IntE D _
    convert h3 using 1
    ring
  · exact key 1 h1

theorem exists_lam {D : D7} {q : ℕ} (hq : q.Prime) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hP0 : P ≠ ⊥)
    (hσ : ∀ a ∈ P, sgO D a ∈ P) {w : 𝓞 D.host.E} (hw1 : w + sgO D w = 1)
    (hw : ∀ Q : Ideal (𝓞 D.host.E), Q.IsPrime → (q : 𝓞 D.host.E) ∈ Q → w - sgO D w ∉ Q)
    {c : 𝓞 D.host.E} (hc : c ∉ P)
    (hcQ : ∀ Q : Ideal (𝓞 D.host.E), Q.IsPrime → (q : 𝓞 D.host.E) ∈ Q → Q ≠ P → c ∈ Q)
    {θ α β : D.host.E} (h : ∀ p ∈ P, IntE D ((p : D.host.E) * θ)) (hθ : ¬ IntE D θ)
    (hα : IntE D α) (hβ : IntE D β) (hα' : D.host.conj α = α) (hβ' : D.host.conj β = β) :
    ∃ (lam : D.host.E) (m : ℕ),
      lam + D.host.conj lam + lam * D.host.conj lam *
        ((c : D.host.E) * D.host.conj c * (α + θ + D.host.conj θ + β)) = 0 ∧ Nat.Coprime m q ∧
      (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧
      ∃ p ∈ P, (m : D.host.E) * (1 + lam * ((c : D.host.E) * D.host.conj c * (α + θ))) = (p : D.host.E) := by
  obtain ⟨a, rfl⟩ := hα
  obtain ⟨b, rfl⟩ := hβ
  set N : 𝓞 D.host.E := c * sgO D c with hN
  have hNE : (N : D.host.E) = (c : D.host.E) * D.host.conj c := rfl
  have hNP : N ∉ P := fun hn => (hP.isPrime.mem_or_mem hn).elim hc (conj_notMem hσ hc)
  set s : 𝓞 D.host.E := (w - sgO D w) - w * (N * (a + b)) with hs
  have hsE : (s : D.host.E) = ((w : D.host.E) - D.host.conj w) -
      (w : D.host.E) * ((c : D.host.E) * D.host.conj c * (algebraMap _ D.host.E a + algebraMap _ D.host.E b)) := rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : D.host.E, μ = (s : D.host.E) - (N : D.host.E) * θ := ⟨_, rfl⟩
  have hμP : ∀ p ∈ P, IntE D ((p : D.host.E) * μ) := fun p hp => by
    rw [hμ, mul_sub, mul_left_comm]
    exact IntE.sub (IntE.mul (intE_coe D p) (intE_coe D s)) (IntE.mul (intE_coe D N) (h p hp))
  have hμn : ¬ IntE D μ := fun hi => hθ <| int_of_mul hP h hNP <| by
    have := IntE.sub (intE_coe D s) hi
    rwa [hμ, sub_sub_cancel] at this
  have hμ0 : μ ≠ 0 := fun h0 => hμn (h0 ▸ zero_mem _)
  have hμ0' : D.host.conj μ ≠ 0 := (map_ne_zero _).2 hμ0
  have hw1E : (w : D.host.E) + D.host.conj w = 1 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hw1
  have htr : μ + D.host.conj μ + (c : D.host.E) * D.host.conj c *
      (algebraMap _ D.host.E a + θ + D.host.conj θ + algebraMap _ D.host.E b) = 0 := by
    rw [hμ, hsE, hNE]
    simp only [map_sub, map_mul, map_add, conj_conj, hα', hβ']
    linear_combination (-((c : D.host.E) * D.host.conj c *
      (algebraMap _ D.host.E a + algebraMap _ D.host.E b))) * hw1E
  obtain ⟨m, hm, r, hr⟩ := exists_nat hq μ (by
    intro Q hQ hqQ
    by_cases hQP : Q = P
    · obtain ⟨p, -, a', ha', e⟩ := exists_mul_notMem hP0 hμP hμn
      exact ⟨p, a', hQP ▸ ha', e⟩
    · have hnle : ¬ P ≤ Q := fun hle => hQP (hP.eq_of_le hQ.ne_top hle).symm
      obtain ⟨p, hp, hpQ⟩ := Set.not_subset.1 hnle
      obtain ⟨t, ht⟩ := h p hp
      have ht' : (t : D.host.E) = (p : D.host.E) * θ := ht
      have hNQ : N ∈ Q := Q.mul_mem_right _ (hcQ Q hQ hqQ hQP)
      refine ⟨p, p * s - N * t, fun hmem => ?_, ?_⟩
      · have h1 : p * (w - sgO D w) ∈ Q := by
          have : p * (w - sgO D w) = (p * s - N * t) + N * (t + p * w * (a + b)) := by rw [hs]; ring
          rw [this]
          exact Q.add_mem hmem (Q.mul_mem_right _ hNQ)
        exact (hQ.mem_or_mem h1).elim hpQ (hw Q hQ hqQ)
      · have : ((p * s - N * t : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) * s - (N : D.host.E) * t := rfl
        rw [this, ht', hμ]; ring)
  have hrP : r ∈ P := by
    by_contra hn
    exact hμn (int_of_mul hP hμP hn (hr ▸ natCast_mem _ m))
  refine ⟨μ⁻¹, m, ?_, hm, ⟨r, hrP, ?_⟩, r * (s + N * a), P.mul_mem_right _ hrP, ?_⟩
  · rw [map_inv₀]
    field_simp
    linear_combination htr
  · rw [hr, mul_assoc, mul_inv_cancel₀ hμ0, mul_one]
  · have : ((r * (s + N * a) : 𝓞 D.host.E) : D.host.E) =
        (r : D.host.E) * ((s : D.host.E) + (N : D.host.E) * algebraMap _ D.host.E a) := rfl
    rw [this, hr, ← hNE, mul_assoc, mul_add μ, ← mul_assoc μ, mul_inv_cancel₀ hμ0, hμ]
    ring

theorem hE_osmul_left (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D (a • x) y = (a : D.host.E) * hE D x y := by
  rw [← algebraMap_smul D.host.E a x, hE_smul_left]

theorem hE_osmul_right (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D x (a • y) = D.host.conj a * hE D x y := by
  rw [← algebraMap_smul D.host.E a y, hE_smul_right]

theorem exists_vectors : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → (∀ a ∈ P, sgO D a ∈ P) → ∀ (B : Lat D n) (x : Fin n → D.host.E), SD D B → NbD D P B x → ∃ (b x' : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), B = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b} ∧ nbr D B x = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x'} ∧ (∀ p ∈ P, p • b ∈ nbM D B x ∧ p • x' ∈ nbM D B x) ∧ ¬ IntE D (hE D b x') ∧ NbD D P B (b + x') ∧ nbM D B (b + x') = nbM D B x ∧ lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x') (b + x') = 0 ∧ Nat.Coprime m q ∧ (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧ ∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x')) = (p : D.host.E) := by
  intro D n q hq P hP hqP hσ B x hB ⟨hxB, hPx, hxx⟩
  obtain ⟨-, -, hdual⟩ := (sd_iff D B).1 hB
  have hq0 : (q : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hP0 : P ≠ ⊥ := fun h0 => hq0 (by rwa [h0, Ideal.mem_bot] at hqP)
  obtain ⟨w, hw1, hw⟩ := GlobalTheory.TraceOne.exists_trace_one D q hq
  obtain ⟨c, hc, hcQ⟩ := exists_c hP hq0
  have hBB : ∀ y ∈ B, ∀ z ∈ B, IntE D (hE D y z) := fun y hy => (hdual y).1 hy
  have hPy : ∀ y ∈ B, ∀ p ∈ P, IntE D ((p : D.host.E) * hE D y x) := fun y hy p hp => by
    have := hBB y hy _ (hPx _ (hσ p hp))
    rwa [hE_osmul_right, sgO_coe, conj_conj] at this
  obtain ⟨b₀, hb₀, hθ₀⟩ : ∃ b₀ ∈ B, ¬ IntE D (hE D b₀ x) := by
    by_contra hcon
    push_neg at hcon
    exact hxB ((hdual x).2 fun y hy => by
      have := (hcon y hy).conj
      rwa [conj_hE] at this)
  obtain ⟨u, hu, hutr⟩ := exists_u hP hP0 hσ (hw P hP.isPrime hqP) (hPy b₀ hb₀) hθ₀
  obtain ⟨b₁, hb₁, hθ₁, htr₁⟩ : ∃ b₁ ∈ B, ¬ IntE D (hE D b₁ x) ∧ IntE D (hE D b₁ x + D.host.conj (hE D b₁ x)) :=
    ⟨u • b₀, B.smul_mem u hb₀, by rwa [hE_osmul_left], by rwa [hE_osmul_left]⟩
  obtain ⟨lam, m, hlam, hm, h1, h2⟩ := exists_lam hq hP hP0 hσ hw1 hw hc hcQ (hPy b₁ hb₁) hθ₁
    (hBB b₁ hb₁ b₁ hb₁) hxx (conj_hE D _ _) (conj_hE D _ _)
  have hb : c • b₁ ∈ B := B.smul_mem c hb₁
  have hPxM : ∀ p ∈ P, p • x ∈ nbM D B x := fun p hp =>
    ⟨hPx p hp, by rw [hE_osmul_left]; exact IntE.mul (intE_coe D p) hxx⟩
  have hcθ : ¬ IntE D (hE D (c • b₁) x) := fun hi => hθ₁ (int_of_mul hP (hPy b₁ hb₁) hc (by
    rw [hE_osmul_left] at hi; exact hi))
  have hcx : ∀ y ∈ B, IntE D (hE D y (c • x)) ↔ IntE D (hE D y x) := fun y hy => by
    rw [hE_osmul_right]
    exact ⟨fun hi => int_of_mul hP (hPy y hy) (conj_notMem hσ hc) hi, fun hi => IntE.mul (intE_coe D c).conj hi⟩
  obtain ⟨v, p₀, hp₀, e₀⟩ := hP.exists_inv hc
  have hx : x = p₀ • x + v • c • x := by rw [smul_smul, ← add_smul, add_comm, e₀, one_smul]
  have hPcx : ∀ p ∈ P, p • c • x ∈ nbM D B x := fun p hp => by
    rw [smul_smul]; exact hPxM _ (P.mul_mem_right c hp)
  have hsq : hE D (c • b₁ + c • x) (c • b₁ + c • x) = (c : D.host.E) * D.host.conj c *
      (hE D b₁ b₁ + hE D b₁ x + D.host.conj (hE D b₁ x) + hE D x x) := by
    rw [← smul_add, hE_osmul_left, hE_osmul_right, hE_add_left, hE_add_right, hE_add_right, conj_hE]
    ring
  refine ⟨c • b₁, c • x, lam, m, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, hm, h1, ?_⟩
  · refine le_antisymm (fun y hy => ?_) (sup_le (fun y hy => hy.1) ((Submodule.span_singleton_le_iff_mem _ _).2 hb))
    obtain ⟨t, ht⟩ := exists_sub_mul hP hP0 (hPy _ hb) hcθ (hPy y hy)
    refine Submodule.mem_sup.2 ⟨y - t • c • b₁, ⟨B.sub_mem hy (B.smul_mem t hb), ?_⟩, t • c • b₁,
      Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
    rw [sub_eq_add_neg, ← neg_smul, hE_add_left, hE_osmul_left]
    have e : ((-t : 𝓞 D.host.E) : D.host.E) = -(t : D.host.E) := rfl
    rw [e, neg_mul, ← sub_eq_add_neg]
    exact ht
  · refine le_antisymm (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
      (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
    · exact Submodule.mem_sup.2 ⟨_, hPxM p₀ hp₀, _,
        Submodule.smul_mem _ v (Submodule.mem_span_singleton_self _), hx.symm⟩
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
  · intro p hp
    exact ⟨⟨B.smul_mem p hb, by rw [hE_osmul_left]; exact hPy _ hb p hp⟩, hPcx p hp⟩
  · rw [hcx _ hb]; exact hcθ
  · intro hmem
    have : c • x ∈ B := by simpa using B.sub_mem hmem hb
    exact hxB (hx ▸ B.add_mem (hPx p₀ hp₀) (B.smul_mem v this))
  · intro p hp
    rw [smul_add]
    exact B.add_mem (B.smul_mem p hb) (hPcx p hp).1
  · rw [hsq, add_assoc (hE D b₁ b₁)]
    exact IntE.mul (IntE.mul (intE_coe D c) (intE_coe D c).conj)
      (IntE.add (IntE.add (hBB b₁ hb₁ b₁ hb₁) htr₁) hxx)
  · ext y
    rw [mem_nbM, mem_nbM]
    refine and_congr_right fun hy => ?_
    rw [← hcx y hy, hE_add_right]
    refine ⟨fun hi => ?_, fun hi => IntE.add (hBB y hy _ hb) hi⟩
    have := IntE.sub hi (hBB y hy _ hb)
    rwa [add_sub_cancel_left] at this
  · rw [hsq]; exact hlam
  · obtain ⟨p, hp, e⟩ := h2
    refine ⟨p, hp, ?_⟩
    rw [← e, ← smul_add, hE_osmul_left, hE_osmul_right, hE_add_right]
    ring

end GlobalTheory.NbVec
