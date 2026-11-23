import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarMemLocR

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicGenus

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def Cyc (A B : Submodule R W) (I : Ideal R) : Prop :=
  ∃ x ∈ A, (∀ y ∈ A, ∃ a : R, y - a • x ∈ B) ∧ ∀ r : R, r • x ∈ B ↔ r ∈ I

theorem cyc_of_equiv {A B : Submodule R W} {I : Ideal R}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) : Cyc A B I := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
  have hx' : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk 1 := by rw [hx]; simp
  refine ⟨x, x.2, fun y hy => ?_, fun r => ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨a, ?_⟩
    have : (Submodule.Quotient.mk (⟨y, hy⟩ - a • x) : A ⧸ B.comap A.subtype) = 0 := by
      apply e.injective
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hx', ← ha,
        ← Submodule.Quotient.mk_smul]
      simp
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · have : r • (x : W) ∈ B ↔ (Submodule.Quotient.mk (r • x) : A ⧸ B.comap A.subtype) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]; rfl
    rw [this, ← EmbeddingLike.map_eq_zero_iff (f := e), Submodule.Quotient.mk_smul, map_smul, hx',
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]

theorem exists_inj {A B : Submodule R W} {I : Ideal R} (x : W) (hx : x ∈ A)
    (hI : ∀ r : R, r • x ∈ B ↔ r ∈ I) :
    ∃ f : (R ⧸ I) →ₗ[R] (A ⧸ B.comap A.subtype), Function.Injective f ∧
      ∀ r : R, f (Submodule.Quotient.mk r) = Submodule.Quotient.mk (r • ⟨x, hx⟩) := by
  let φ : R →ₗ[R] (A ⧸ B.comap A.subtype) :=
    LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk ⟨x, hx⟩)
  have hφ : ∀ r, φ r = Submodule.Quotient.mk (r • ⟨x, hx⟩) := fun r => by
    rw [Submodule.Quotient.mk_smul]; rfl
  have hk : LinearMap.ker φ = I := by
    ext r
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, ← hI]; rfl
  refine ⟨Submodule.liftQ I φ hk.ge, ?_, fun r => hφ r⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ hk.le

theorem equiv_of_cyc {A B : Submodule R W} {I : Ideal R} (h : Cyc A B I) :
    Nonempty ((A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) := by
  obtain ⟨x, hx, h1, h2⟩ := h
  obtain ⟨f, hf, hf'⟩ := exists_inj x hx h2
  refine ⟨(LinearEquiv.ofBijective f ⟨hf, fun q => ?_⟩).symm⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := h1 y y.2
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  rw [hf', eq_comm, Submodule.Quotient.eq]
  exact ha

theorem Cyc.smul_mem {A B : Submodule R W} {I : Ideal R} (h : Cyc A B I) {r : R} (hr : r ∈ I)
    {y : W} (hy : y ∈ A) : r • y ∈ B := by
  obtain ⟨x, -, h1, h2⟩ := h
  obtain ⟨a, ha⟩ := h1 y hy
  have : r • y = r • (y - a • x) + a • (r • x) := by rw [smul_sub, smul_comm a r x]; abel
  rw [this]
  exact B.add_mem (B.smul_mem r ha) (B.smul_mem a ((h2 r).2 hr))

theorem Cyc.localise {M' L' M : Submodule R W} {I P : Ideal R} (h : Cyc M' L' I) (hP : P.IsMaximal)
    (S : Submonoid R) (hS : ∀ s ∈ S, s ∉ P) (hIP : I ≤ P) (hPI : ∀ r ∈ P, ∃ t ∈ S, t * r ∈ I)
    (hM : locS S M' = locS S M) : Cyc M (M ⊓ locS S L') P := by
  obtain ⟨x, hx, h1, h2⟩ := h
  have inv : ∀ s ∈ S, ∃ u, 1 - u * s ∈ P := fun s hs => by
    obtain ⟨u, p, hp, e⟩ := hP.exists_inv (hS s hs)
    exact ⟨u, by rw [← e]; simpa using hp⟩
  obtain ⟨s, hs, hsx⟩ : x ∈ locS S M := hM ▸ locBasic_le_locS S M' hx
  refine ⟨s • x, hsx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => ⟨M.smul_mem r hsx, ?_⟩⟩⟩
  · obtain ⟨t, ht, hty⟩ : y ∈ locS S M' := hM.symm ▸ locBasic_le_locS S M hy
    obtain ⟨a, ha⟩ := h1 _ hty
    obtain ⟨u, hu⟩ := inv _ (S.mul_mem ht hs)
    obtain ⟨t', ht', hu'⟩ := hPI _ hu
    refine ⟨u * a, M.sub_mem hy (M.smul_mem _ hsx), t' * t, S.mul_mem ht' ht, ?_⟩
    have : (t' * t) • (y - (u * a) • s • x) =
        t' • (t • y - a • x) + a • ((t' * (1 - u * (t * s))) • x) := by module
    rw [this]
    exact L'.add_mem (L'.smul_mem _ ha) (L'.smul_mem _ ((h2 _).2 hu'))
  · obtain ⟨t, ht, htx⟩ := hr.2
    rw [smul_smul, smul_smul, h2] at htx
    have := hIP htx
    rcases hP.isPrime.mem_or_mem this with h | h
    · exact (hP.isPrime.mem_or_mem h).resolve_left (hS t ht)
    · exact absurd h (hS s hs)
  · obtain ⟨t, ht, htr⟩ := hPI r hr
    refine ⟨t, ht, ?_⟩
    rw [smul_smul, smul_smul, h2]
    exact I.mul_mem_right _ htr

theorem exists_ann {A B : Submodule R W} (s : Finset (Ideal R)) (hs : ∀ P ∈ s, P.IsMaximal)
    (hk : ∀ r : R, (∀ P ∈ s, r ∈ P) → ∀ y ∈ A, r • y ∈ B)
    (hn : ∀ P ∈ s, ∀ r : R, r ∉ P → ∃ y ∈ A, r • y ∉ B) :
    ∃ x ∈ A, ∀ r : R, r • x ∈ B ↔ ∀ P ∈ s, r ∈ P := by
  have he : ∀ P ∈ s, ∃ e : R, e ∉ P ∧ ∀ Q ∈ s, Q ≠ P → e ∈ Q := by
    intro P hP
    have : ¬ ((s.erase P).inf id ≤ P) := by
      intro hle
      obtain ⟨Q, hQ, hQP⟩ := ((hs P hP).isPrime.inf_le').1 hle
      rw [Finset.mem_erase] at hQ
      exact hQ.1 ((hs Q hQ.2).eq_of_le (hs P hP).ne_top hQP)
    obtain ⟨e, h1, h2⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨e, h2, fun Q hQ hne => (Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, hQ⟩)) h1⟩
  choose! e he1 he2 using he
  have hy : ∀ P ∈ s, ∃ y ∈ A, e P • y ∉ B := fun P hP => hn P hP _ (he1 P hP)
  choose! y hy1 hy2 using hy
  have hxA : ∑ P ∈ s, e P • y P ∈ A := A.sum_mem fun P hP => A.smul_mem _ (hy1 P hP)
  refine ⟨_, hxA, fun r => ⟨fun hr P hP => ?_, fun hr => hk r hr _ hxA⟩⟩
  by_contra hrP
  have h1 : (e P * r) • ∑ Q ∈ s, e Q • y Q ∈ B := by rw [mul_smul]; exact B.smul_mem _ hr
  rw [← Finset.add_sum_erase s _ hP, smul_add] at h1
  have h2 : (e P * r) • ∑ Q ∈ s.erase P, e Q • y Q ∈ B := by
    rw [Finset.smul_sum]
    refine B.sum_mem fun Q hQ => ?_
    rw [Finset.mem_erase] at hQ
    rw [smul_smul]
    refine hk _ (fun P' hP' => ?_) _ (hy1 Q hQ.2)
    by_cases h : P' = P
    · subst h
      exact P'.mul_mem_left _ (he2 Q hQ.2 P' hP' (Ne.symm hQ.1))
    · exact P'.mul_mem_right _ (P'.mul_mem_right _ (he2 P hP P' hP' h))
  have h3 : (e P * r) • e P • y P ∈ B := by simpa using B.sub_mem h1 h2
  have h4 : e P * r ∉ P := fun h => ((hs P hP).isPrime.mem_or_mem h).elim (he1 P hP) hrP
  obtain ⟨u, p, hp, hu⟩ := (hs P hP).exists_inv h4
  apply hy2 P hP
  have : e P • y P = u • ((e P * r) • e P • y P) + (p * e P) • y P := by
    rw [smul_smul u, mul_smul p, ← add_smul, hu, one_smul]
  rw [this]
  refine B.add_mem (B.smul_mem _ h3) (hk _ (fun P' hP' => ?_) _ (hy1 P hP))
  by_cases h : P' = P
  · subst h
    exact P'.mul_mem_right _ hp
  · exact P'.mul_mem_left _ (he2 P hP P' hP' h)

end General

section Primes

variable {K : Type} [Field K] [NumberField K] [StarRing K]

noncomputable abbrev cj : 𝓞 K →+* 𝓞 K := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range

theorem cj_cj (r : 𝓞 K) : cj (cj r) = r := genusCovol_hinj (by
  rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])

theorem mem_conj {P : Ideal (𝓞 K)} {r : 𝓞 K} : r ∈ conjIdeal (K := K) P ↔ cj r ∈ P := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]

theorem conj_conj (P : Ideal (𝓞 K)) : conjIdeal (K := K) (conjIdeal (K := K) P) = P := by
  ext r
  rw [mem_conj, mem_conj, cj_cj]

theorem conj_eq_map (P : Ideal (𝓞 K)) : conjIdeal (K := K) P = P.map cj := by
  apply le_antisymm
  · intro r hr
    rw [← cj_cj r]
    exact Ideal.mem_map_of_mem _ (mem_conj.1 hr)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_conj, cj_cj]
    exact hr

theorem conj_mono {P Q : Ideal (𝓞 K)} (h : P ≤ Q) : conjIdeal (K := K) P ≤ conjIdeal (K := K) Q :=
  fun _ hr => mem_conj.2 (h (mem_conj.1 hr))

theorem conj_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (conjIdeal (K := K) P).IsMaximal := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]
  exact Ideal.comap_isMaximal_of_surjective _ (Function.Involutive.surjective cj_cj)

theorem conj_prod (s : Finset (Ideal (𝓞 K))) :
    conjIdeal (K := K) (∏ P ∈ s, P) = ∏ P ∈ s, conjIdeal (K := K) P := by
  simp only [conj_eq_map]
  exact map_prod (Ideal.mapHom cj) _ s

theorem hcompl_conj (P : Ideal (𝓞 K)) :
    hcompl (K := K) (conjIdeal (K := K) P) = hcompl (K := K) P := by
  have key : ∀ (Q : Ideal (𝓞 K)) (s : 𝓞 K),
      (∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ Q) ↔ cj s ∉ Q := by
    intro Q s
    constructor
    · intro H; exact H _ (locBasic_sigma_spec _ _ s)
    · intro H t e
      have : t = cj s := genusCovol_hinj (by rw [locBasic_sigma_spec, e])
      rwa [this]
  unfold hcompl
  congr 1
  ext s
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, key, key, mem_conj, mem_conj, cj_cj]
  exact and_comm

theorem conj_ne (hK : IsCMUnram K) {T : ℕ} (hT : T.Prime) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hN : Ideal.absNorm P = T) : conjIdeal (K := K) P ≠ P := by
  intro e
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  have ht' : t = cj θ := genusCovol_hinj (by rw [locBasic_sigma_spec, ht])
  have hc : Nat.card (𝓞 K ⧸ P) = T := by rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  letI := Fintype.ofFinite (𝓞 K ⧸ P)
  let φ := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hT (by rw [← hc, Nat.card_eq_fintype_card])
  obtain ⟨z, hz⟩ := φ.surjective (Ideal.Quotient.mk P θ)
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk P), eq_comm, Ideal.Quotient.eq] at hz
  have h2 : cj (θ - (n : 𝓞 K)) ∈ P := by rw [← mem_conj, e]; exact hz
  rw [map_sub, map_intCast, ← ht'] at h2
  apply hθ
  simpa using P.sub_mem hz h2

omit [StarRing K] in

theorem exists_primes {T : ℕ} (hT : T.Prime)
    (H : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) :
    ∃ S : Finset (Ideal (𝓞 K)), (∀ P, P ∈ S ↔ P.IsMaximal ∧ (T : 𝓞 K) ∈ P) ∧
      ∏ P ∈ S, P = Ideal.span {(T : 𝓞 K)} ∧ S.card = Module.finrank ℚ K := by
  have h0 : Ideal.span {(T : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hT.ne_zero
  have hmax : ∀ P : Ideal (𝓞 K), P.IsPrime → (T : 𝓞 K) ∈ P → P.IsMaximal := fun P hP hTP =>
    hP.isMaximal (by rintro rfl; exact hT.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hTP)))
  have hsq : Squarefree (Ideal.span {(T : 𝓞 K)}) := by
    rw [squarefree_iff_no_irreducibles h0]
    intro P hP hd
    have hP' : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP)
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at hd
    have hTP : (T : 𝓞 K) ∈ P := Ideal.mul_le_left hd
    exact (H P (hmax P hP' hTP) hTP).2 (by rwa [pow_two])
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).1 hsq
  let S : Finset (Ideal (𝓞 K)) := ⟨_, hnd⟩
  have hm : ∀ P, P ∈ S ↔ P.IsMaximal ∧ (T : 𝓞 K) ∈ P := fun P => by
    change P ∈ UniqueFactorizationMonoid.normalizedFactors _ ↔ _
    rw [Ideal.mem_normalizedFactors_iff h0, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun h => ⟨hmax P h.1 h.2, h.2⟩, fun h => ⟨h.1.isPrime, h.2⟩⟩
  have hp : ∏ P ∈ S, P = Ideal.span {(T : 𝓞 K)} := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    exact Ideal.prod_normalizedFactors_eq_self h0
  refine ⟨S, hm, hp, ?_⟩
  have := congrArg Ideal.absNorm hp
  rw [map_prod, Finset.prod_congr rfl (fun P hP => (H P ((hm P).1 hP).1 ((hm P).1 hP).2).1),
    Finset.prod_const, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
  exact Nat.pow_right_injective hT.two_le this

theorem exists_half (hK : IsCMUnram K) {T : ℕ} (hT : T.Prime)
    (H : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧
      IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧
      (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)} := by
  obtain ⟨S, hm, hp, hc⟩ := exists_primes hT H
  let e : Ideal (𝓞 K) ↪ Cardinal := embeddingToCardinal
  let s := S.filter fun P => e P < e (conjIdeal (K := K) P)
  have hS : ∀ P ∈ S, conjIdeal (K := K) P ∈ S := fun P hP =>
    (hm _).2 ⟨conj_isMaximal ((hm P).1 hP).1, mem_conj.2 (by rw [map_natCast]; exact ((hm P).1 hP).2)⟩
  have hinj : Function.Injective (conjIdeal (K := K) (R := 𝓞 K)) :=
    Function.Involutive.injective conj_conj
  have him : s.image (conjIdeal (K := K)) = S.filter fun P => ¬ e P < e (conjIdeal (K := K) P) := by
    ext P
    simp only [s, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨Q, ⟨hQ, hlt⟩, rfl⟩
      exact ⟨hS Q hQ, by rw [conj_conj]; exact hlt.not_gt⟩
    · rintro ⟨hP, hlt⟩
      refine ⟨_, ⟨hS P hP, ?_⟩, conj_conj P⟩
      rw [conj_conj]
      have h1 := (hm P).1 hP
      exact lt_of_le_of_ne (not_lt.1 hlt) fun h => conj_ne hK hT h1.1 (H P h1.1 h1.2).1 (e.injective h)
  have hsm : ∀ P ∈ s, P.IsMaximal := fun P hP => ((hm P).1 (Finset.mem_filter.1 hP).1).1
  refine ⟨s, ?_, fun P hP => ?_, ?_, ?_⟩
  · have h1 := Finset.card_filter_add_card_filter_not (s := S) fun P => e P < e (conjIdeal (K := K) P)
    rw [← him, Finset.card_image_of_injective _ hinj, hc] at h1
    have := hK.1
    have h2 := IsTotallyComplex.finrank (K := K)
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
    change s.card + s.card = _ at h1
    unfold fDeg
    omega
  · have h1 := (hm P).1 (Finset.mem_filter.1 hP).1
    exact ⟨h1.1, (H P h1.1 h1.2).1⟩
  · rw [conj_prod]
    refine IsCoprime.prod_left fun P hP => IsCoprime.prod_right fun Q hQ => ?_
    refine Ideal.isCoprime_iff_sup_eq.2 ((hsm P hP).coprime_of_ne (conj_isMaximal (hsm Q hQ)) ?_)
    rintro rfl
    have h1 := (Finset.mem_filter.1 hP).2
    rw [conj_conj] at h1
    exact h1.not_gt (Finset.mem_filter.1 hQ).2
  · rw [conj_prod, ← hp, ← Finset.prod_filter_mul_prod_filter_not S (fun P => e P < e (conjIdeal (K := K) P)),
      ← him, Finset.prod_image (fun _ _ _ _ h => hinj h)]

end Primes

section Lattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [FiniteDimensional K V] in
theorem Cyc.gmap {A B : Submodule (𝓞 K) V} {I : Ideal (𝓞 K)} (H : Cyc A B I) (g : V ≃ₗ[K] V) :
    Cyc (gmap g A) (gmap g B) I := by
  obtain ⟨x, hx, h1, h2⟩ := H
  have hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v := fun r v =>
    LinearMapClass.map_smul_of_tower g.symm r v
  refine ⟨g x, ?_, fun y hy => ?_, fun r => ?_⟩
  · rw [isomAct_mem_gmap]; simpa using hx
  · rw [isomAct_mem_gmap] at hy
    obtain ⟨a, ha⟩ := h1 _ hy
    refine ⟨a, ?_⟩
    rw [isomAct_mem_gmap, map_sub, hg]
    simpa using ha
  · rw [isomAct_mem_gmap, hg, ← h2]
    simp

omit [NumberField K] [FiniteDimensional K V] in

theorem transfer (g : V ≃ₗ[K] V) {A B A' B' : Submodule (𝓞 K) V} (hA : gmap g A = A') (hB : gmap g B = B')
    (r : 𝓞 K) : (∀ y ∈ A, r • y ∈ B) ↔ ∀ y ∈ A', r • y ∈ B' := by
  have hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v := fun r v =>
    LinearMapClass.map_smul_of_tower g.symm r v
  subst hA hB
  constructor
  · intro H y hy
    rw [isomAct_mem_gmap] at hy ⊢
    rw [hg]
    exact H _ hy
  · intro H y hy
    have := H (g y) (by rw [isomAct_mem_gmap]; simpa using hy)
    rw [isomAct_mem_gmap, hg] at this
    simpa using this

theorem smul_loc {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R)
    {A B : Submodule R W} {r : R} (H : ∀ y ∈ A, r • y ∈ B) : ∀ y ∈ locS S A, r • y ∈ locS S B := by
  rintro y ⟨s, hs, hy⟩
  exact ⟨s, hs, by rw [smul_comm]; exact H _ hy⟩

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hK hs hn

theorem forward (T : 𝓞 K) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal)
    (hp : ∏ P ∈ S, P = Ideal.span {T}) (L N : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (eL : (↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {T}))
    (hN : N ∈ genus h L) :
    IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {T})) := by
  obtain ⟨h0, -, -, hg, -⟩ := DiscOrder.main K V h hK hs hn L hL
  obtain ⟨hNi, hd⟩ := hg N hN
  refine ⟨hNi, ?_⟩
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hc := cyc_of_equiv eL
  have hinf : ∀ r : 𝓞 K, (∀ P ∈ S, r ∈ P) ↔ r ∈ Ideal.span {T} := by
    intro r
    rw [← hp, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp
    · intro P hP Q hQ hne
      exact Ideal.isCoprime_iff_sup_eq.2 ((hS P hP).coprime_of_ne (hS Q hQ) hne)
  have tr : ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ r : 𝓞 K,
      (∀ y ∈ loc (K := K) P (dual h L), r • y ∈ loc (K := K) P L) ↔
        ∀ y ∈ loc (K := K) P (dual h N), r • y ∈ loc (K := K) P N := by
    intro P hP r
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    refine transfer g ?_ hgL r
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg L
    have b1 := (ld (gmap g L) (a5.2 hL.1).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h L)).2.1 P]
  obtain ⟨x, hx, hxa⟩ := exists_ann (A := dual h N) (B := N) S hS
    (fun r hr y hy => genusBasic_lg (K := K) N _ fun P hP =>
      (tr P hP r).1 (smul_loc _ fun z hz => hc.smul_mem ((hinf r).1 hr) hz) y (locBasic_le_locS _ _ hy))
    (fun P hP r hr => by
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, -, hz2⟩ := hc
      obtain ⟨t, ht, htz⟩ := (tr P (hS P hP) r).2 (smul_loc _ hcon) z (locBasic_le_locS _ _ hz)
      rw [smul_smul, hz2, ← hinf] at htz
      exact ((hS P hP).isPrime.mem_or_mem (htz P hP)).elim (genusBasic_hS P (hS P hP) t ht) hr)
  obtain ⟨f, hf, -⟩ := exists_inj x hx (I := Ideal.span {T}) fun r => (hxa r).trans (hinf r)
  have c1 : Nat.card (↥(dual h N) ⧸ N.comap (dual h N).subtype) = Nat.card (𝓞 K ⧸ Ideal.span {T}) := by
    rw [← Nat.card_congr eL.toEquiv]
    exact hd
  have : Finite (↥(dual h N) ⧸ N.comap (dual h N).subtype) := Nat.finite_of_card_ne_zero (by
    change discN h N ≠ 0
    rwa [hd])
  exact ⟨(LinearEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, c1.symm⟩)).symm⟩

theorem backward (s : Finset (Ideal (𝓞 K))) (hm : ∀ P ∈ s, P.IsMaximal)
    (hco : IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)))
    (L N M M' : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M')
    (uM : IsUnimodular h M) (uM' : IsUnimodular h M') (hLM : L ≤ M) (hNM : N ≤ M')
    (cL : Cyc M L (∏ P ∈ s, P)) (cN : Cyc M' N (∏ P ∈ s, P)) : SameGenus h L N := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have key : ∀ P ∈ s, ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P N := by
    intro P hPs
    have hP := hm P hPs
    have hP' := conj_isMaximal hP
    have u' := (ld M' hM'.fg).2.1 uM' P hP
    obtain ⟨g, hg, hgM⟩ := UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP
      ((ld M hM.fg).2.1 uM P hP) u'
    have hle : ∀ Q ∈ s, ∏ P ∈ s, P ≤ Q := fun Q hQ => Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun P => P) hQ)
    have hIP := hle P hPs
    have hIc : ¬ ∏ P ∈ s, P ≤ conjIdeal (K := K) P := fun hle =>
      hP'.ne_top (top_le_iff.1 ((Ideal.isCoprime_iff_sup_eq.1 hco).ge.trans (sup_le hle (conj_mono hIP))))
    have hne : conjIdeal (K := K) P ≠ P := fun e => hIc (hIP.trans e.ge)
    obtain ⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K := K) P, t ∈ ∏ Q ∈ s.erase P, Q := by
      have c1 : IsCoprime (∏ Q ∈ s.erase P, Q) P := IsCoprime.prod_left fun Q hQ =>
        Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP
          (Finset.ne_of_mem_erase hQ))
      have c2 : IsCoprime (∏ Q ∈ s.erase P, Q) (conjIdeal (K := K) P) := IsCoprime.prod_left fun Q hQ =>
        Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP' fun e =>
          hIc ((hle Q (Finset.mem_of_mem_erase hQ)).trans e.le))
      obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 (c1.mul_right c2)
      refine ⟨a, locBasic_mem_hcompl P a (fun h => hP.ne_top ?_) (fun h => hP'.ne_top ?_), ha⟩
      · rw [Ideal.eq_top_iff_one, ← hab]; exact P.add_mem h (Ideal.mul_le_inf hb).1
      · rw [Ideal.eq_top_iff_one, ← hab]; exact Ideal.add_mem _ h (Ideal.mul_le_inf hb).2
    have hPI : ∀ r ∈ P, ∃ t ∈ hcompl (K := K) P, t * r ∈ ∏ Q ∈ s, Q := fun r hr =>
      ⟨t, ht, by rw [← Finset.prod_erase_mul s _ hPs]; exact Ideal.mul_mem_mul htI hr⟩
    have a1 := (isomAct (𝓞 K) K V h g hg M).2.1 P
    have a2 := (isomAct (𝓞 K) K V h g hg L).2.1 P
    have d1 := (cL.gmap g).localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI (a1.trans hgM)
    have d2 := cN.localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI rfl
    obtain ⟨g', hg', -, hg2⟩ := GlobalTheory.Mass.Hyperplane.main K V h hK hs hn M' hM' P hP hne u' _ _ inf_le_left inf_le_left
      (equiv_of_cyc d1) (equiv_of_cyc d2)
    refine ⟨g' * g, (isom h).mul_mem hg' hg, ?_⟩
    have l1 : loc (K := K) P (gmap g L) ≤ loc (K := K) P M' := by
      rw [← hgM, ← a1]
      exact locBasic_locS_mono _ (Submodule.map_mono hLM)
    unfold loc at hg2 l1 a2 ⊢
    rw [locBasic_locS_inf, locBasic_locS_inf, locBasic_locS_idem, locBasic_locS_idem, inf_eq_right.2 l1,
      inf_eq_right.2 (locBasic_locS_mono _ hNM)] at hg2
    rw [genusBasic_gmap_mul, ← a2, hg2]
  intro P hP
  have hP' := conj_isMaximal hP
  have mem : ∀ Q : Ideal (𝓞 K), Q.IsMaximal → ∏ P ∈ s, P ≤ Q → Q ∈ s := fun Q hQ hle => by
    obtain ⟨Q', hQ', hle'⟩ := (hQ.isPrime.prod_le).1 hle
    rwa [← (hm Q' hQ').eq_of_le hQ.ne_top hle']
  by_cases h1 : ∏ P ∈ s, P ≤ P
  · exact key P (mem P hP h1)
  by_cases h2 : ∏ P ∈ s, P ≤ conjIdeal (K := K) P
  · have := key _ (mem _ hP' h2)
    unfold loc at this ⊢
    rwa [hcompl_conj] at this
  obtain ⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K := K) P, t ∈ ∏ Q ∈ s, Q := by
    obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
    obtain ⟨b, hb, hb'⟩ := SetLike.not_le_iff_exists.1 h2
    by_cases hac : a ∈ conjIdeal (K := K) P
    · by_cases hbp : b ∈ P
      · refine ⟨a + b, locBasic_mem_hcompl P _ (fun h => ha' ?_) (fun h => hb' ?_), Ideal.add_mem _ ha hb⟩
        · simpa using P.sub_mem h hbp
        · simpa using (conjIdeal (K := K) P).sub_mem h hac
      · exact ⟨b, locBasic_mem_hcompl P _ hbp hb', hb⟩
    · exact ⟨a, locBasic_mem_hcompl P _ ha' hac, ha⟩
  have eq : ∀ {A B : Submodule (𝓞 K) V}, B ≤ A → Cyc A B (∏ P ∈ s, P) →
      loc (K := K) P B = loc (K := K) P A := fun hle hc =>
    le_antisymm (locBasic_locS_mono _ hle)
      ((locBasic_locS_mono _ fun y hy => locBasic_mem_locS.2 ⟨t, ht, hc.smul_mem htI hy⟩).trans (locBasic_locS_idem _ _).le)
  rw [eq hLM cL, eq hNM cN]
  exact UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP
    ((ld M hM.fg).2.1 uM P hP) ((ld M' hM'.fg).2.1 uM' P hP)

end Lattices

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → (∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧ IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧ (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)}) ∧ ∀ L N : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → (N ∈ genus h L ↔ IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}))) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hn T hT H
  refine ⟨exists_half hK hT H, fun L N hL ⟨eL⟩ => ⟨fun hN => ?_, fun ⟨hN, eN⟩ => ⟨hN.1, ?_⟩⟩⟩
  · obtain ⟨S, hm, hp, -⟩ := exists_primes hT H
    exact forward h hK hs hn _ S (fun P hP => ((hm P).1 hP).1) hp L N hL eL hN
  · obtain ⟨s, -, hm, hco, hp⟩ := exists_half hK hT H
    have h0 : ∏ P ∈ s, P ≠ ⊥ := by
      intro e
      rw [e, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hp
      exact hT.ne_zero (by exact_mod_cast hp)
    have one := (GlobalTheory.Mass.SplitOver.main K V h hK hs hn _ h0 hco).1
    rw [hp] at one
    obtain ⟨M, ⟨hM, uM, hLM, ⟨cL⟩⟩, -⟩ := one L hL ⟨eL⟩
    obtain ⟨M', ⟨hM', uM', hNM, ⟨cN⟩⟩, -⟩ := one N hN eN
    exact backward h hK hs hn s (fun P hP => (hm P hP).1) hco L N M M' hM hM' uM uM' hLM hNM
      (cyc_of_equiv cL) (cyc_of_equiv cN)

end GlobalTheory.Mass.CyclicGenus
