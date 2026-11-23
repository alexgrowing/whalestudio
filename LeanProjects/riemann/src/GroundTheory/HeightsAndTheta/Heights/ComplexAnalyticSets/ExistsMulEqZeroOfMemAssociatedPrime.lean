import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRegularElement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatNormalFibres
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

theorem weaklyRegular_eq_nil_of_socle {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {z : M} (hz : z ≠ 0) (hk : ∀ r ∈ maximalIdeal R, r • z = 0) {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsWeaklyRegular M rs) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    exfalso
    have h := ((isWeaklyRegular_cons_iff M r rs).mp hreg).1
    exact hz (h (show r • z = r • (0 : M) by rw [hk r (hm r List.mem_cons_self), smul_zero]))

theorem algebraMap_not_mem_map_of_colon_le {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r, r * y ∈ I → r ∈ Q) :
    algebraMap B (Localization.AtPrime Q) y ∉ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro h
  obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl] at hs
  obtain ⟨c, hc⟩ := hs
  have h1 : (↑c * ↑s) * y ∈ I := by
    rw [show (↑c * ↑s) * y = ↑c * (y * ↑s) by ring, hc]
    exact I.mul_mem_left _ i.2
  have h2 := hy _ h1
  exact (Q.primeCompl.mul_mem c.2 s.2) h2

theorem mul_algebraMap_mem_map_of_le_colon {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r ∈ Q, r * y ∈ I) :
    ∀ m ∈ maximalIdeal (Localization.AtPrime Q),
      m * algebraMap B (Localization.AtPrime Q) y ∈ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro m hm
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
  have hle : Q.map (algebraMap B (Localization.AtPrime Q)) ≤
      (I.map (algebraMap B (Localization.AtPrime Q))).colon {algebraMap B (Localization.AtPrime Q) y} := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hy r hr)
  have := hle hm
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this

theorem ringKrullDim_le_zero_of_socle {L : Type*} [CommRing L] [IsLocalRing L] (hS : SerreSAt L 2)
    {z : L} (hz : z ≠ 0) (hk : ∀ m ∈ maximalIdeal L, m * z = 0) : ringKrullDim L ≤ 0 := by
  obtain ⟨rs, hm, hreg, hlen⟩ := hS
  have := weaklyRegular_eq_nil_of_socle hz (fun m hm => by rw [smul_eq_mul]; exact hk m hm) hm hreg
  subst this
  simp only [List.length_nil, Nat.cast_zero] at hlen
  exact (min_le_iff.mp hlen).resolve_left (by decide)

theorem exists_mul_eq_zero_of_mem_associatedPrime {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hR : SerreR B 1) (hS : SerreS B 2) {Q : Ideal B} (hQ : IsAssociatedPrime Q B) {q : B} (hq : q ∈ Q) :
    ∃ t ∉ Q, t * q = 0 := by
  obtain ⟨hprime, y, rfl⟩ := isAssociatedPrime_iff.mp hQ
  set Q := (⊥ : Submodule B B).colon {y} with hQdef
  have hmem : ∀ r, r ∈ Q ↔ r * y = 0 := fun r => by
    rw [hQdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  let L := Localization.AtPrime Q
  have hz : algebraMap B L y ≠ 0 := by
    have := algebraMap_not_mem_map_of_colon_le Q ⊥ (y := y) (fun r hr => (hmem r).mpr (by simpa using hr))
    simpa [Ideal.map_bot] using this
  have hk : ∀ m ∈ maximalIdeal L, m * algebraMap B L y = 0 := fun m hm => by
    have := mul_algebraMap_mem_map_of_le_colon Q ⊥ (y := y) (fun r hr => by simpa using (hmem r).mp hr) m hm
    simpa [Ideal.map_bot] using this
  have hdim := ringKrullDim_le_zero_of_socle (hS Q) hz hk
  have hreg : IsRegularLocalRing L := hR Q (hdim.trans (by decide))
  have hsf := (isRegularLocalRing_iff L).mp hreg
  have h0 : (maximalIdeal L).spanFinrank = 0 := by
    have : ((maximalIdeal L).spanFinrank : WithBot ℕ∞) ≤ 0 := hsf ▸ hdim
    exact Nat.le_zero.mp (by exact_mod_cast this)
  have hbot : maximalIdeal L = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal L).fg_of_isNoetherianRing).mp h0
  have hqm : algebraMap B L q ∈ maximalIdeal L := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L Q]
    exact hq
  rw [hbot, Submodule.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hqm
  obtain ⟨⟨t, ht⟩, htq⟩ := hqm
  exact ⟨t, ht, htq⟩

theorem ringKrullDim_le_one_of_colon_span {B : Type*} [CommRing B] [IsNoetherianRing B] (hS : SerreS B 2)
    {b y : B} (hb : b ∈ nonZeroDivisors B) (Q : Ideal B) [Q.IsPrime]
    (hQ : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b}) : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hbQ : b ∈ Q := (hQ b).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b))
  have hbm : f b ∈ maximalIdeal L := (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hbQ
  have hbL : f b ∈ nonZeroDivisors L :=
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hb)
  have hbreg : IsSMulRegular L (f b) := fun u v huv => by
    simp only [smul_eq_mul] at huv
    have : (u - v) * f b = 0 := by rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hbL).mp this)
  have hmap : (Ideal.span {b}).map f = Ideal.span {f b} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsm : ∀ z : L, z ∈ f b • (⊤ : Submodule L L) ↔ z ∈ Ideal.span {f b} := fun z => by
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨w, by rw [← hw, smul_eq_mul, mul_comm]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, trivial, by rw [smul_eq_mul, mul_comm, hw]⟩
  let zb : QuotSMulTop (f b) L := Submodule.Quotient.mk (f y)
  have hz : zb ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, hsm, ← hmap] at h
    exact algebraMap_not_mem_map_of_colon_le Q _ (fun r hr => (hQ r).mpr hr) h
  have hk : ∀ m ∈ maximalIdeal L, m • zb = 0 := fun m hm => by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, ← hmap, smul_eq_mul]
    exact mul_algebraMap_mem_map_of_le_colon Q _ (fun r hr => (hQ r).mp hr) m hm
  obtain ⟨rs, hm, hreg, hlen⟩ := hS Q
  obtain ⟨rs', hlen', hm', hreg'⟩ := GroundTheory.Heights₂.Heights.exists_isRegular_quotSMulTop hm hreg hbreg hbm
  have hnil := weaklyRegular_eq_nil_of_socle hz hk hm' hreg'.toIsWeaklyRegular
  subst hnil
  simp only [List.length_nil] at hlen'
  have h1 : rs.length ≤ 1 := by omega
  have h2 : min (2 : WithBot ℕ∞) (ringKrullDim L) ≤ 1 := hlen.trans (by exact_mod_cast h1)
  exact (min_le_iff.mp h2).resolve_left (by decide)

theorem isReduced_of_serre {B : Type*} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1) (hS : SerreS B 2) :
    IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B x hx0
  have hprime : Q.IsPrime := hQ.isPrime
  obtain ⟨n, hn⟩ := hx
  have hxQ : x ∈ Q := hprime.mem_of_pow_mem n (by rw [hn]; exact Q.zero_mem)
  obtain ⟨t, ht, htx⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ hxQ
  exact ht (hle (by rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htx))

theorem isIntegrallyClosed_of_serre {B : Type} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsIntegrallyClosed B := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective (FractionRing B) le_rfl, fun {x} hx => ?_⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) x
  suffices ha : a ∈ Ideal.span {b} by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hc]⟩
  by_contra ha
  have ha0 : (Ideal.Quotient.mk (Ideal.span {b}) a) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B _ ha0
  obtain ⟨hprime, yb, hyb⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hcol : ∀ r z : B, r ∈ (⊥ : Submodule B (B ⧸ Ideal.span {b})).colon {Ideal.Quotient.mk _ z} ↔
      r * z ∈ Ideal.span {b} := fun r z => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, map_mul,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hQy : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b} := fun r => by rw [hyb, hcol]
  have haQ : ∀ r, r * a ∈ Ideal.span {b} → r ∈ Q := fun r hr => hle ((hcol r a).mpr hr)
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hdim := ringKrullDim_le_one_of_colon_span hS hb Q hQy
  have : IsRegularLocalRing L := hR Q hdim
  have : IsDomain L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hic : IsIntegrallyClosed L :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one hdim
  have hnz : ∀ s ∈ nonZeroDivisors B, f s ∈ nonZeroDivisors L := fun s hs =>
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hs)
  let K := FractionRing L
  let g : B →+* K := (algebraMap L K).comp f
  have hg : ∀ s : nonZeroDivisors B, IsUnit (g s) := fun s =>
    IsLocalization.map_units K (⟨f s, hnz s s.2⟩ : nonZeroDivisors L)
  let φ : FractionRing B →+* K := IsLocalization.lift hg
  have hφ : ∀ r, φ (algebraMap B (FractionRing B) r) = g r := IsLocalization.lift_eq hg
  have hint : IsIntegral L (φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap L K).comp f = φ.comp (algebraMap B (FractionRing B)) from
      (IsLocalization.lift_comp hg).symm, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have h1 : φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩) * g b = g a := by
    rw [← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
  have h2 : c * f b = f a := IsFractionRing.injective L K (by rw [map_mul, hc]; exact h1)
  apply algebraMap_not_mem_map_of_colon_le Q (Ideal.span {b}) haQ
  rw [← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self b))

theorem isDomain_of_serre {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsDomain B := by
  have hred : IsReduced B := isReduced_of_serre hR hS
  have hic : IsIntegrallyClosed B := isIntegrallyClosed_of_serre hR hS
  refine @NoZeroDivisors.to_isDomain B _ _ ⟨fun {u v} huv => ?_⟩
  by_contra! h
  obtain ⟨hu, hv⟩ := h
  let J : Ideal B := Ideal.span {u} ⊔ (⊥ : Submodule B B).colon {u}
  have hJ : ∃ s ∈ J, s ∈ nonZeroDivisors B := by
    by_contra! hJ
    have hsub : (J : Set B) ⊆ ⋃ p ∈ associatedPrimes B B, (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact fun s hs => hJ s hs
    obtain ⟨Q, hQ, hJQ⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite B B) (f := id) ⊥ ⊥
      (fun Q hQ _ _ => hQ.isPrime)).mp hsub
    obtain ⟨t, ht, htu⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ
      (hJQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)))
    exact ht (hJQ (Ideal.mem_sup_right (by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htu)))
  obtain ⟨s, hsJ, hs⟩ := hJ
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hsJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hwu : w * u = 0 := by
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at hw
  have hxy : r * u * w = 0 := by rw [mul_assoc, mul_comm u w, hwu, mul_zero]
  let e := IsLocalization.mk' (FractionRing B) (r * u) (⟨r * u + w, hs⟩ : nonZeroDivisors B)
  have he : e * e = e := by
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul]
    linear_combination (-(r * u + w)) * hxy
  have hint : IsIntegral B e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, pow_two, he]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have hc' : c * (r * u + w) = r * u := by
    rw [IsLocalization.eq_mk'_iff_mul_eq] at hc
    exact IsLocalization.injective (FractionRing B) le_rfl (by rw [map_mul]; exact hc)
  have h1 : c * (w * w) = 0 := by linear_combination w * hc' + (1 - c) * hxy
  have h2 : (1 - c) * ((r * u) * (r * u)) = 0 := by linear_combination (-(r * u)) * hc' + c * hxy
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc1 | hc1
  · have hw0 : w = 0 := IsReduced.eq_zero w ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h1⟩
    subst hw0
    rw [add_zero] at hs
    apply hv
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp (by rw [mul_assoc, huv, mul_zero])
  · have hx0 : r * u = 0 := IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h2⟩
    rw [hx0, zero_add] at hs
    exact hu ((mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp hwu)

theorem SerreNormalOfRegularDepth.proof : SerreNormalOfRegularDepth.Statement := by
  intro A _ hA hR hS P _
  set B := Localization.AtPrime P
  have hRB : SerreR B 1 := fun Q _ =>
    (hR (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  have hSB : SerreS B 2 := fun Q _ =>
    (hS (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  exact ⟨isDomain_of_serre hRB hSB, isIntegrallyClosed_of_serre hRB hSB⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
