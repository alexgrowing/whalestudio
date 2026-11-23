import Mathlib

namespace GlobalTheory

open PrimeSpectrum

namespace SpanGenLocus

theorem notMem_support_quotient_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum R) (N : Submodule R M) :
    q ∉ Module.support R (M ⧸ N) ↔ ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ N := by
  rw [Module.notMem_support_iff']
  constructor
  · intro h x
    obtain ⟨t, ht, e⟩ := h (Submodule.Quotient.mk x)
    exact ⟨t, ht, (Submodule.Quotient.mk_eq_zero N).1 (by rw [Submodule.Quotient.mk_smul]; exact e)⟩
  · intro h y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    obtain ⟨t, ht, e⟩ := h x
    exact ⟨t, ht, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact e⟩

theorem linIndep_at_of_gen_at {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (q : PrimeSpectrum R) {r : ℕ}
    (hr : Module.rankAtStalk M q = r) (n : Fin r → M)
    (hgen : ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ Submodule.span R (Set.range n))
    (c : Fin r → R) (hc : ∑ i, c i • n i = 0) : ∃ t ∉ q.asIdeal, ∀ i, t * c i = 0 := by
  let Rq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule q.asIdeal.primeCompl M
  haveI : Module.Free Rq Mq := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  let n' : Fin r → Mq := fun i => LocalizedModule.mk (n i) 1
  have hspan : Submodule.span Rq (Set.range n') = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    induction y using LocalizedModule.induction_on with
    | h x u =>
      obtain ⟨t, ht, hx⟩ := hgen x
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
      have e1 : LocalizedModule.mk x u =
          (Localization.mk (1 : R) (⟨t, ht⟩ * u) : Rq) • LocalizedModule.mk (t • x) 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
        exact (LocalizedModule.mk_cancel_common_left ⟨t, ht⟩ u x).symm
      have e2 : (LocalizedModule.mk (t • x) 1 : Mq) = ∑ i, (algebraMap R Rq (a i)) • n' i := by
        rw [← ha]
        simp only [n', algebraMap_smul]
        rw [← LocalizedModule.mkLinearMap_apply, map_sum]
        simp [LocalizedModule.mkLinearMap_apply]
      rw [e1, e2]
      exact Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let L : (Fin r → Rq) →ₗ[Rq] Mq := Fintype.linearCombination Rq n'
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hspan
  have hrk : Module.finrank Rq Mq = r := hr
  let b := Module.finBasisOfFinrankEq Rq Mq hrk
  have hinj : Function.Injective L := by
    have h2 : Function.Surjective (b.equivFun.toLinearMap ∘ₗ L) :=
      b.equivFun.surjective.comp hL
    have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
    exact fun x y hxy => h3 (by simp [hxy])
  have hz : L (fun i => algebraMap R Rq (c i)) = 0 := by
    simp only [L, Fintype.linearCombination_apply, n', algebraMap_smul]
    have h0 : (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) (∑ i, c i • n i) = 0 := by
      rw [hc, map_zero]
    simpa [map_sum, LocalizedModule.mkLinearMap_apply] using h0
  have hz' : (fun i => algebraMap R Rq (c i)) = 0 := hinj (by rw [hz, map_zero])
  have hi : ∀ i, ∃ τ : q.asIdeal.primeCompl, (τ : R) * c i = 0 := fun i =>
    (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl Rq (c i)).1 (congrFun hz' i)
  choose τ hτ using hi
  refine ⟨∏ j, (τ j : R), q.asIdeal.primeCompl.prod_mem (fun j _ => (τ j).2), fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (τ j : R)) (Finset.mem_univ i)
  rw [hk, mul_comm (τ i : R) k, mul_assoc, hτ i, mul_zero]

theorem exists_gen_near {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (p : PrimeSpectrum R) {r : ℕ}
    (hr : Module.rankAtStalk M p = r) :
    ∃ m : Fin r → M, ∃ f ∉ p.asIdeal, ∀ x : M, f • x ∈ Submodule.span R (Set.range m) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule p.asIdeal.primeCompl M
  haveI : Module.Free Rp Mp := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  have hrk : Module.finrank Rp Mp = r := hr
  let b := Module.finBasisOfFinrankEq Rp Mp hrk
  have hmk : ∀ y : Mp, ∃ (x : M) (u : p.asIdeal.primeCompl), LocalizedModule.mk x u = y :=
    fun y => LocalizedModule.induction_on (fun x u => ⟨x, u, rfl⟩) y
  choose m u hmu using fun i => hmk (b i)
  let N := Submodule.span R (Set.range m)
  have htop : Submodule.span Rp (Set.range fun i => (LocalizedModule.mk (m i) 1 : Mp)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (Localization.mk (1 : R) (u i) : Rp) • LocalizedModule.mk (m i) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, hmu]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hgen : ∀ x : M, ∃ t ∉ p.asIdeal, t • x ∈ N := by
    intro x
    have hx : (LocalizedModule.mk x 1 : Mp) ∈
        N.localized' Rp p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) := by
      rw [Submodule.localized'_span, ← Set.range_comp]
      rw [show ((LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) ∘ m) =
        fun i => (LocalizedModule.mk (m i) 1 : Mp) from rfl, htop]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 hx
    have h2 : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) y s =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) x (1 : p.asIdeal.primeCompl) := by
      rw [IsLocalizedModule.mk'_one, LocalizedModule.mkLinearMap_apply]; exact hs
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at h2
    obtain ⟨c, hc⟩ := h2
    refine ⟨(c : R) * s, p.asIdeal.primeCompl.mul_mem c.2 s.2, ?_⟩
    have e : ((c : R) * s) • x = (c : R) • y := by
      simpa [Submonoid.smul_def, mul_smul] using hc
    rw [e]; exact N.smul_mem _ hy
  have hq : p ∉ Module.support R (M ⧸ N) := (notMem_support_quotient_iff p N).2 hgen
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hq
  obtain ⟨f, hf, hfp⟩ := hq
  refine ⟨m, f, hfp, fun x => ?_⟩
  have := Module.mem_annihilator.1 hf (Submodule.Quotient.mk x)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

theorem exists_local_det {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] {r : ℕ}
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) (s : Fin r → M)
    (p : PrimeSpectrum R) :
    ∃ f g : R, f ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum R, f ∉ q.asIdeal →
      (q ∉ Module.support R (M ⧸ Submodule.span R (Set.range s)) ↔ g ∉ q.asIdeal) := by
  obtain ⟨m, f, hfp, hfm⟩ := exists_gen_near p (hr p)
  have ha : ∀ i, ∃ a : Fin r → R, ∑ j, a j • m j = f • s i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hfm (s i))
  choose a ha using ha
  let A : Matrix (Fin r) (Fin r) R := Matrix.of fun j i => a i j
  have hK : ∀ u : Fin r → R, ∑ j, (A.mulVec u) j • m j = f • ∑ i, u i • s i := by
    intro u
    calc ∑ j, (A.mulVec u) j • m j = ∑ j, ∑ i, u i • (a i j • m j) := by
          simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, mul_smul]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ∑ i, u i • ∑ j, a i j • m j := by rw [Finset.sum_comm]; simp [Finset.smul_sum]
      _ = ∑ i, u i • f • s i := by simp [ha]
      _ = f • ∑ i, u i • s i := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨f, A.det, hfp, fun q hfq => ?_⟩
  rw [notMem_support_quotient_iff]
  constructor
  · intro hgen
    have hgm : ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ Submodule.span R (Set.range m) :=
      fun x => ⟨f, hfq, hfm x⟩
    have hcol : ∀ j, ∃ τ : R, τ ∉ q.asIdeal ∧ ∃ w : Fin r → R, A.mulVec w = Pi.single j τ := by
      intro j
      obtain ⟨t, ht, hts⟩ := hgen (m j)
      obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hts
      have h1 := hK w
      rw [hw] at h1
      have hsingle : ∑ k, (Pi.single j (f * t) : Fin r → R) k • m k = f • t • m j := by
        rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
        simp [mul_smul]
      obtain ⟨τ, hτ, hτc⟩ := linIndep_at_of_gen_at q (hr q) m hgm
        (A.mulVec w - Pi.single j (f * t)) (by
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, hsingle, sub_self])
      refine ⟨τ * (f * t), q.asIdeal.primeCompl.mul_mem hτ
        (q.asIdeal.primeCompl.mul_mem hfq ht), τ • w, ?_⟩
      funext k
      have hk := hτc k
      rw [Pi.sub_apply, mul_sub, sub_eq_zero] at hk
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hk]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    choose τ hτ w hw using hcol
    let B : Matrix (Fin r) (Fin r) R := Matrix.of fun k j => w j k
    have hAB : A * B = Matrix.diagonal τ := by
      ext k j
      have h := congrFun (hw j) k
      simp only [Matrix.mulVec, dotProduct] at h
      rw [Matrix.mul_apply]
      simp only [B, Matrix.of_apply]
      rw [h, Matrix.diagonal_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    have hprod : A.det * B.det ∉ q.asIdeal := by
      rw [← Matrix.det_mul, hAB, Matrix.det_diagonal]
      exact q.asIdeal.primeCompl.prod_mem (fun j _ => hτ j)
    exact fun hA => hprod (q.asIdeal.mul_mem_right _ hA)
  · intro hdet x
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hfm x)
    have hAu : A.mulVec (A.adjugate.mulVec v) = A.det • v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 := hK (A.adjugate.mulVec v)
    rw [hAu] at h1
    have h2 : ∑ j, (A.det • v) j • m j = (A.det * f) • x := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hv]
    refine ⟨A.det * f, q.asIdeal.primeCompl.mul_mem hdet hfq, ?_⟩
    rw [← h2, h1]
    exact Submodule.smul_mem _ _ ((Submodule.mem_span_range_iff_exists_fun R).2 ⟨_, rfl⟩)

end SpanGenLocus

open SpanGenLocus

theorem isCompact_compl_support_quotient_span :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) →
      ∀ s : Fin r → M, IsCompact (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ := by
  intro R M _ _ _ _ _ r hr s
  choose f g hf hfg using fun p => exists_local_det hr s p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (basicOpen (f p) : Set (PrimeSpectrum R))) (fun p => (basicOpen (f p)).isOpen)
    (fun p _ => Set.mem_iUnion.2 ⟨p, hf p⟩)
  have heq : (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ =
      ⋃ p ∈ t, (basicOpen (f p * g p) : Set (PrimeSpectrum R)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, mem_basicOpen, exists_prop]
    constructor
    · intro hq
      obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      have hqp' : f p ∉ q.asIdeal := hqp
      exact ⟨p, hp, q.asIdeal.primeCompl.mul_mem hqp' ((hfg p q hqp').1 hq)⟩
    · rintro ⟨p, -, hpq⟩
      have h1 : f p ∉ q.asIdeal := fun h => hpq (q.asIdeal.mul_mem_right _ h)
      have h2 : g p ∉ q.asIdeal := fun h => hpq (q.asIdeal.mul_mem_left _ h)
      exact (hfg p q h1).2 h2
  rw [heq]
  exact t.isCompact_biUnion fun p _ => isCompact_basicOpen _

end GlobalTheory
