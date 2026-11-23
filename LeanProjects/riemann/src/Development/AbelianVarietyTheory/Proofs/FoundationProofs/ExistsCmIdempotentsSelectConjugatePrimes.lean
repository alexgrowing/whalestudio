import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.SelectIdem

section Ring

variable {R : Type*} [CommRing R]

def LocDvd (P : Ideal R) (n x : R) : Prop := ∃ s, s ∉ P ∧ n ∣ s * x

theorem dvd_of_locDvd {n x : R} (h : ∀ P : Ideal R, P.IsMaximal → LocDvd P n x) : n ∣ x := by
  by_contra hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R R x) (Ideal.span {n})
  have hI : ∀ s, s ∈ I ↔ n ∣ s * x := fun s => by
    simp [I, Ideal.mem_span_singleton]
  have hne : I ≠ ⊤ := fun h1 => hx (by
    have : (1 : R) ∈ I := h1 ▸ Submodule.mem_top
    simpa using (hI 1).1 this)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨s, hs, hd⟩ := h P hP
  exact hs (hIP ((hI s).2 hd))

theorem LocDvd.comb {P : Ideal R} (hP : P.IsPrime) {n x y z : R} (a b : R)
    (hx : LocDvd P n x) (hy : LocDvd P n y) (hz : z = a * x + b * y) : LocDvd P n z := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  have : s * t * z = (t * a) * (s * x) + (s * b) * (t * y) := by rw [hz]; ring
  rw [this]
  exact dvd_add (hs'.mul_left _) (ht'.mul_left _)

theorem LocDvd.of_dvd {P : Ideal R} {n m x : R} (h : n ∣ m) (hx : LocDvd P m x) :
    LocDvd P n x := by
  obtain ⟨s, hs, hs'⟩ := hx
  exact ⟨s, hs, h.trans hs'⟩

theorem LocDvd.of_not_mem {P : Ideal R} {n : R} (h : n ∉ P) (x : R) : LocDvd P n x :=
  ⟨n, h, dvd_mul_right _ _⟩

theorem exists_loc [IsDedekindDomain R] {n : R} (hn : n ≠ 0) (T : Ideal R → Prop) :
    ∃ ε : R, ∀ P : Ideal R, P.IsMaximal → LocDvd P n (ε - if T P then 1 else 0) := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => 1)
    (fun P hP => by
      obtain ⟨h1, h2⟩ := (hS P).1 hP
      refine Ideal.prime_of_isPrime ?_ h1
      rintro rfl
      exact hn (by simpa using h2))
    (fun _ _ _ _ h => h) (fun P => if T P.1 then 1 else 0)
  have hb' : ∀ P : Ideal R, P.IsPrime → n ∈ P → b - (if T P then 1 else 0) ∈ P := fun P h1 h2 => by
    simpa using hb P ((hS P).2 ⟨h1, h2⟩)
  have hrad : (1 - b) * b ∈ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨h1, h2⟩
    have h3 := hb' P h2 ((Ideal.span_singleton_le_iff_mem _).1 h1)
    by_cases hT : T P
    · rw [if_pos hT] at h3
      have : (1 - b) * b = (-b) * (b - 1) := by ring
      rw [this]; exact P.mul_mem_left _ h3
    · rw [if_neg hT, sub_zero] at h3
      exact P.mul_mem_left _ h3
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton, mul_pow] at hk
  have hc : IsCoprime (1 - b) b := ⟨1, 1, by ring⟩
  obtain ⟨u, v, huv⟩ := hc.pow (m := k) (n := k)
  refine ⟨v * b ^ k, fun P hP => ?_⟩
  by_cases hnP : n ∈ P
  · have h3 := hb' P hP.isPrime hnP
    by_cases hT : T P
    · rw [if_pos hT] at h3 ⊢
      refine ⟨b ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.sub_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : b ^ k * (v * b ^ k - 1) = (-u) * ((1 - b) ^ k * b ^ k) := by
          linear_combination b ^ k * huv
        rw [this]; exact hk.mul_left _
    · rw [if_neg hT, sub_zero] at h3 ⊢
      refine ⟨(1 - b) ^ k, fun h => ?_, ?_⟩
      · have h4 := hP.isPrime.mem_of_pow_mem k h
        have : (1 : R) ∈ P := by simpa using P.add_mem h4 h3
        exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
      · have : (1 - b) ^ k * (v * b ^ k) = v * ((1 - b) ^ k * b ^ k) := by ring
        rw [this]; exact hk.mul_left _
  · exact LocDvd.of_not_mem hnP _

theorem exists_select [IsDedekindDomain R] [CharZero R] {G : Type*} [Group G]
    [MulSemiringAction G R] (c : G) (hc : c * c = 1) :
    ∃ e : ℕ → R, (∀ N m : ℕ, 0 < N → 0 < m → (N : R) ∣ e (N * m) - e N) ∧
      (∀ N : ℕ, 0 < N → (N : R) ∣ e N * e N - e N ∧ (N : R) ∣ e N * (c • e N)) ∧
      ∀ N : ℕ, 0 < N →
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P = P) → (N : R) ∣ e N + c • e N) ∧
        ((∀ P : Ideal R, P.IsMaximal → (N : R) ∈ P → c • P ≠ P) →
          (N : R) ∣ 1 - (e N + c • e N)) := by
  let T : Ideal R → Prop := fun P => WellOrderingRel P (c • P)
  have hcc : ∀ P : Ideal R, c • c • P = P := fun P => by rw [smul_smul, hc, one_smul]
  have hT1 : ∀ P, T P → ¬ T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h1 h2
    exact asymm h1 h2
  have hT2 : ∀ P, c • P ≠ P → ¬ T P → T (c • P) := fun P h1 h2 => by
    simp only [T, hcc] at h2 ⊢
    rcases trichotomous_of WellOrderingRel P (c • P) with h | h | h
    · exact (h2 h).elim
    · exact (h1 h.symm).elim
    · exact h
  have hT3 : ∀ P, c • P = P → ¬ T P := fun P h1 h2 => hT1 P h2 (h1.symm ▸ h2)
  have hex : ∀ N : ℕ, ∃ ε : R, 0 < N →
      ∀ P : Ideal R, P.IsMaximal → LocDvd P (N : R) (ε - if T P then 1 else 0) := fun N => by
    by_cases hN : 0 < N
    · obtain ⟨ε, h⟩ := exists_loc (n := (N : R)) (by exact_mod_cast hN.ne') T
      exact ⟨ε, fun _ => h⟩
    · exact ⟨0, fun h => (hN h).elim⟩
  choose e he using hex
  have he' : ∀ N : ℕ, 0 < N → ∀ P : Ideal R, P.IsMaximal →
      LocDvd P (N : R) (c • e N - if T (c • P) then 1 else 0) := fun N hN P hP => by
    have hP' : (c • P).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (MulSemiringAction.toRingHom G R c)
        (MulAction.surjective c) hP with h | h
      · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) c).ne_top
      · exact h
    obtain ⟨s, hs, t, ht⟩ := he N hN _ hP'
    refine ⟨c • s, fun h => hs ?_, c • t, ?_⟩
    · have := Ideal.smul_mem_pointwise_smul c _ _ h
      rwa [smul_smul, hc, one_smul] at this
    · have h := congrArg (MulSemiringAction.toRingHom G R c) ht
      simp only [map_mul, map_sub, map_natCast, MulSemiringAction.toRingHom_apply] at h
      rw [← h]
      split_ifs <;> simp
  refine ⟨e, fun N m hN hm => ?_, fun N hN => ⟨?_, ?_⟩, fun N hN => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine dvd_of_locDvd fun P hP => ?_
    exact LocDvd.comb hP.isPrime 1 (-1)
      ((he (N * m) (Nat.mul_pos hN hm) P hP).of_dvd (by push_cast; exact dvd_mul_right _ _))
      (he N hN P hP) (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    by_cases hT : T P
    · rw [if_pos hT] at h
      exact LocDvd.comb hP.isPrime (e N) 0 h h (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (e N - 1) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    have h := he N hN P hP
    have h' := he' N hN P hP
    by_cases hT : T P
    · rw [if_neg (hT1 P hT)] at h'
      exact LocDvd.comb hP.isPrime (e N) 0 h' h' (by ring)
    · rw [if_neg hT] at h
      exact LocDvd.comb hP.isPrime (c • e N) 0 h h (by ring)
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      rw [h3] at h2
      rw [if_neg (hT3 P h3)] at h1 h2
      exact LocDvd.comb hP.isPrime 1 1 h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _
  · refine dvd_of_locDvd fun P hP => ?_
    by_cases hNP : (N : R) ∈ P
    · have h1 := he N hN P hP
      have h2 := he' N hN P hP
      have h3 := h P hP hNP
      by_cases hT : T P
      · rw [if_pos hT] at h1
        rw [if_neg (hT1 P hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
      · rw [if_neg hT] at h1
        rw [if_pos (hT2 P h3 hT)] at h2
        exact LocDvd.comb hP.isPrime (-1) (-1) h1 h2 (by ring)
    · exact LocDvd.of_not_mem hNP _

end Ring

theorem smul_eq_of_abelian {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
    (hcomm : ∀ σ τ : E ≃ₐ[ℚ] E, σ * τ = τ * σ) (c : E ≃ₐ[ℚ] E) {q : ℕ} (hq : q.Prime)
    (P Q : Ideal (𝓞 E)) (hP : P.IsPrime) (hQ : Q.IsPrime) (hqP : (q : 𝓞 E) ∈ P)
    (hqQ : (q : 𝓞 E) ∈ Q) (h : c • P = P) : c • Q = Q := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP hqP
  haveI := key Q hQ hqQ
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [smul_smul, hcomm, ← smul_smul, h]

theorem exists_select_idem : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  have hc : D.host.conj * D.host.conj = 1 := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine AlgEquiv.ext fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  obtain ⟨e, h1, h2, h3⟩ := exists_select (R := 𝓞 D.host.E) D.host.conj hc
  refine ⟨e, h1, h2, fun q k hq => ?_⟩
  have hq' : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((q ^ k : ℕ) : 𝓞 D.host.E) ∈ P →
      (q : 𝓞 D.host.E) ∈ P := fun P hP h =>
    hP.isPrime.mem_of_pow_mem k (by simpa using h)
  obtain ⟨h4, h5⟩ := h3 (q ^ k) (pow_pos hq.pos k)
  refine ⟨fun hI => h4 fun P hP h => hI P hP.isPrime ?_ (hq' P hP h), fun hI => h5 fun P hP h hfix => hI ?_⟩
  · rintro rfl
    have := hq' _ hP h
    rw [Ideal.mem_bot] at this
    exact hq.ne_zero (by exact_mod_cast this)
  · intro Q hQ _ hqQ
    exact smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ (hq' P hP h) hqQ hfix

end GlobalTheory.SelectIdem
