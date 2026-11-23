import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LocalNorm

theorem exists_add_mul_sq_eq_of_norm {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {c e : K} (hc : ‖c‖ ≤ 1) (he : ‖e‖ < 1) : ∃ t, t + c * t ^ 2 = e := by
  have hsf : Set.MapsTo (fun t : K => e - c * t ^ 2) (Metric.closedBall 0 ‖e‖)
      (Metric.closedBall 0 ‖e‖) := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht ⊢
    beta_reduce
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h0 := norm_nonneg t
    have h1 : ‖t‖ ^ 2 ≤ ‖e‖ := by nlinarith
    nlinarith [norm_nonneg c, sq_nonneg ‖t‖]
  have hcon : ContractingWith ‖e‖₊ (hsf.restrict _ _ _) := by
    refine ⟨by exact_mod_cast he, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx := mem_closedBall_zero_iff.1 x.2
    have hy := mem_closedBall_zero_iff.1 y.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [Set.MapsTo.val_restrict_apply, coe_nnnorm]
    have h1 : e - c * (x : K) ^ 2 - (e - c * (y : K) ^ 2)
        = -(c * ((x : K) + y) * ((x : K) - y)) := by ring
    have h2 : ‖(x : K) + y‖ ≤ ‖e‖ := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    rw [h1, norm_neg, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    nlinarith [norm_nonneg c, norm_nonneg ((x : K) + y)]
  obtain ⟨t, -, ht, -⟩ := hcon.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hsf
    (x := 0) (Metric.mem_closedBall_self (norm_nonneg e)) (edist_ne_top _ _)
  have ht' : e - c * t ^ 2 = t := ht
  exact ⟨t, by linear_combination -ht'⟩

theorem exists_binary_eq_adicCompletion {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {a n u : 𝓞 F}
    (hD : a ^ 2 - 4 * n ∉ v.asIdeal) (hu : u ∉ v.asIdeal) :
    ∃ r s : v.adicCompletion F, r ^ 2 + algebraMap F _ (a : F) * r * s
      + algebraMap F _ (n : F) * s ^ 2 = algebraMap F _ (u : F) := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  obtain ⟨r, s, hrs⟩ := UnramifiedHermitian.exists_binary_eq_of_finite
    (a := Ideal.Quotient.mk v.asIdeal a) (n := Ideal.Quotient.mk v.asIdeal n)
    (by
      intro h
      apply hD
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa only [map_sub, map_mul, map_pow, map_ofNat] using h)
    (Ideal.Quotient.mk v.asIdeal u)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hN : u - (r ^ 2 + a * r * s + n * s ^ 2) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq]
    simpa only [map_add, map_mul, map_pow] using hrs.symm
  have hN' : r ^ 2 + a * r * s + n * s ^ 2 ∉ v.asIdeal := fun h => hu (by
    simpa using v.asIdeal.add_mem hN h)
  set φ : 𝓞 F →+* v.adicCompletion F := (algebraMap F _).comp (algebraMap (𝓞 F) F) with hφ
  have hval : ∀ z : 𝓞 F, Valued.v (φ z) = v.intValuation z := fun z => by
    rw [← v.valuation_of_algebraMap (K := F), ← v.valuedAdicCompletion_eq_valuation' (K := F)]
    rfl
  have hle : ∀ z, ‖φ z‖ ≤ 1 := fun z => by
    rw [Valued.toNormedField.norm_le_one_iff, hval]; exact v.intValuation_le_one z
  have hlt : ∀ z ∈ v.asIdeal, ‖φ z‖ < 1 := fun z hz => by
    rw [Valued.toNormedField.norm_lt_one_iff, hval]
    exact (v.intValuation_lt_one_iff_mem z).2 hz
  have heq : ∀ z ∉ v.asIdeal, ‖φ z‖ = 1 := fun z hz => by
    refine le_antisymm (hle z) (not_lt.1 fun h => hz ?_)
    rw [Valued.toNormedField.norm_lt_one_iff, hval] at h
    exact (v.intValuation_lt_one_iff_mem z).1 h
  have hD1 := heq _ hD
  have hN1 := heq _ hN'
  have hD0 : φ (a ^ 2 - 4 * n) ≠ 0 := fun h => by simp [h] at hD1
  have hN0 : φ (r ^ 2 + a * r * s + n * s ^ 2) ≠ 0 := fun h => by simp [h] at hN1
  obtain ⟨t, ht⟩ := exists_add_mul_sq_eq_of_norm (K := v.adicCompletion F)
    (c := -(φ n / φ (a ^ 2 - 4 * n)))
    (e := φ (u - (r ^ 2 + a * r * s + n * s ^ 2)) / φ (r ^ 2 + a * r * s + n * s ^ 2))
    (by rw [norm_neg, norm_div, hD1, div_one]; exact hle n)
    (by rw [norm_div, hN1, div_one]; exact hlt _ hN)
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at ht hD0 hN0
  change ∃ r' s', r' ^ 2 + φ a * r' * s' + φ n * s' ^ 2 = φ u
  generalize φ a = A, φ n = N, φ u = U, φ r = R, φ s = S at *
  obtain ⟨y, hy⟩ : ∃ y, (A ^ 2 - 4 * N) * y = 1 := ⟨_, mul_inv_cancel₀ hD0⟩
  have hy' : (A ^ 2 - 4 * N)⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [eq_div_iff hN0, div_eq_mul_inv, hy'] at ht
  refine ⟨R * (1 - 2 * N * y * t) - N * S * (A * y * t),
    R * (A * y * t) + S * (1 - 2 * N * y * t) + A * S * (A * y * t), ?_⟩
  linear_combination ht + (R ^ 2 + A * R * S + N * S ^ 2) * (t - N * y * t ^ 2) * hy

theorem exists_sub_notMem {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.Unramified A B] (σ : B →ₐ[A] B) (hσ : ∃ b, σ b ≠ b) (P : Ideal B) (hP : P ≠ ⊤) :
    ∃ b, b - σ b ∉ P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1
    inferInstance
  obtain ⟨b, hb⟩ := hσ
  set ψ := Algebra.TensorProduct.productMap (AlgHom.id A B) σ with hψ
  have h0 : ψ t = 0 := by
    have := congrArg ψ (ht b)
    simp only [map_mul, map_sub, map_zero, hψ, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, map_one, one_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hb)
  have h1 : ∀ z, Algebra.TensorProduct.lmul' A z - ψ z ∈ P := by
    intro z
    induction z with
    | zero => simp
    | tmul x y =>
      simp only [hψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]
      exact P.mul_mem_left _ (hcon y)
    | add x y hx hy =>
      have := P.add_mem hx hy
      rw [map_add, map_add]
      convert this using 1
      ring
  have := h1 t
  rw [ht1, h0, sub_zero] at this
  exact hP ((Ideal.eq_top_iff_one P).2 this)

theorem exists_local_generator {B : Type*} [CommRing B] [IsDedekindDomain B] {I Q : Ideal B}
    (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) :
    ∃ i ∈ I, ∃ r, r - 1 ∈ Q ∧ Ideal.span {r} * I ≤ Ideal.span {i} := by
  obtain ⟨i, hi⟩ := IsDedekindDomain.exists_sup_span_eq (I := Q * I) (J := I) Ideal.mul_le_right
    (mul_ne_zero hQ hI)
  obtain ⟨r, hr, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := Q)
    (N := Ideal.span {i}) (N' := I) (P := I) (IsNoetherian.noetherian I) le_rfl
    (by rw [sup_comm, smul_eq_mul, hi])
  refine ⟨i, ?_, r, hr, ?_⟩
  · rw [← hi]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self i)
  · rw [Ideal.span_singleton_mul_le_iff]
    exact fun z hz => hle (Submodule.smul_mem_pointwise_smul z r I hz)

theorem exists_mul_eq_of_mem_mul_map {B : Type*} [CommRing B] (σ : B →+* B) {I : Ideal B}
    {i r m : B} (h : Ideal.span {r} * I ≤ Ideal.span {i}) (hm : m ∈ I * I.map σ) :
    ∃ c, c * (i * σ i) = r * σ r * m := by
  have h' := Ideal.map_mono (f := σ) h
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton] at h'
  have h2 := Ideal.mul_mono h h'
  rw [Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm,
    Ideal.span_singleton_mul_span_singleton] at h2
  exact Ideal.mem_span_singleton'.1
    (h2 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm))

theorem exists_eq_sq_add_of_mul_eq {K : Type*} [Field K] {d x a₀ b₀ a₁ b₁ a₂ b₂ : K}
    (h₁ : a₁ ^ 2 + d * b₁ ^ 2 ≠ 0)
    (h : x * (a₁ ^ 2 + d * b₁ ^ 2) = (a₀ ^ 2 + d * b₀ ^ 2) * (a₂ ^ 2 + d * b₂ ^ 2)) :
    ∃ a b, x = a ^ 2 + d * b ^ 2 := by
  refine ⟨((a₀ * a₂ - d * b₀ * b₂) * a₁ - d * (a₀ * b₂ + a₂ * b₀) * b₁) / (a₁ ^ 2 + d * b₁ ^ 2),
    ((a₀ * a₂ - d * b₀ * b₂) * b₁ + (a₀ * b₂ + a₂ * b₀) * a₁) / (a₁ ^ 2 + d * b₁ ^ 2), ?_⟩
  field_simp
  linear_combination (a₁ ^ 2 + d * b₁ ^ 2) * h

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem complexConj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hsq' : IsCMField.complexConj E (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq').resolve_left fun h => ?_
  let φ : E →+* ℂ := Classical.choice inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.1 h1.symm
  have h2 := congrArg φ hsq
  rw [map_pow, ht, map_neg, map_natCast] at h2
  have h3 : t ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg t]

theorem exists_coords (H : Host E) (z : E) : ∃ α β : maximalRealSubfield E,
    ((2 * α : maximalRealSubfield E) : E) = z + IsCMField.complexConj E z ∧
    ((α ^ 2 + H.d * β ^ 2 : maximalRealSubfield E) : E) = z * IsCMField.complexConj E z := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hd : (H.d : E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hrt : (H.rt : E) ≠ 0 := fun h => hd (by simpa [h] using hsq)
  refine ⟨⟨(z + IsCMField.complexConj E z) / 2, (IsCMField.complexConj_eq_self_iff E _).1 ?_⟩,
    ⟨(z - IsCMField.complexConj E z) / (2 * H.rt), (IsCMField.complexConj_eq_self_iff E _).1 ?_⟩,
    ?_, ?_⟩
  · simp only [map_div₀, map_add, map_ofNat, IsCMField.complexConj_apply_apply, add_comm]
  · simp only [map_div₀, map_sub, map_mul, map_ofNat, IsCMField.complexConj_apply_apply,
      complexConj_rt]
    field_simp
    ring
  · push_cast
    change (2 : E) * _ = _
    ring
  · push_cast
    rw [← neg_neg (H.d : E), ← hsq]
    field_simp
    ring

theorem exists_mul_norm_eq (x : maximalRealSubfield E) (hx : x ≠ 0) {I J : Ideal (𝓞 E)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (σ : 𝓞 E →+* 𝓞 E)
    (hσ : ∀ a, ((σ a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    (h : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x : E)
      * ((I * I.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
      = ((J * J.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ (z₁ z₂ : E) (u : 𝓞 (maximalRealSubfield E)), z₁ ≠ 0 ∧ u ∉ v.asIdeal ∧
      (x : E) * (z₁ * IsCMField.complexConj E z₁)
        = ((u : maximalRealSubfield E) : E) * (z₂ * IsCMField.complexConj E z₂) := by
  haveI := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal
    (by simp [RingHom.ker_eq_bot_iff_eq_zero, (RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))])
  set Q := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hQdef
  have hQP : Q ≤ P := Ideal.map_le_iff_le_comap.2 hPv.ge
  have hQ : Q ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hσ' : ∀ a, σ a = IsCMField.ringOfIntegersComplexConj E a := fun a =>
    RingOfIntegers.ext (hσ a)
  have hQσ : Q ≤ Q.comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, hσ', AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hy
  have hone : ∀ r, r - 1 ∈ Q → r ∉ P := fun r hr hrP =>
    hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using P.sub_mem hrP (hQP hr)))
  have hnorm : ∀ r, r - 1 ∈ Q → r * σ r ∉ P := fun r hr hrP =>
    (hP.isPrime.mem_or_mem hrP).elim (hone r hr) (hone _ (by simpa using hQσ hr))
  have hgen : ∀ {K : Ideal (𝓞 E)}, K ≠ ⊥ → ∀ i r : 𝓞 E, r - 1 ∈ Q →
      Ideal.span {r} * K ≤ Ideal.span {i} → (i : E) ≠ 0 := by
    intro K hK i r hr hle hi
    have hi' : i = 0 := by exact_mod_cast hi
    rw [hi', Ideal.span_singleton_zero, le_bot_iff, Ideal.mul_eq_bot,
      Ideal.span_singleton_eq_bot] at hle
    exact hone r hr (by rw [hle.resolve_right hK]; exact P.zero_mem)
  obtain ⟨i, hi, r, hr, hri⟩ := exists_local_generator hI hQ
  obtain ⟨j, hj, s, hs, hsj⟩ := exists_local_generator hJ hQ
  have hi0 := hgen hI i r hr hri
  have hj0 := hgen hJ j s hs hsj
  have hs0 : (s : E) ≠ 0 := fun h0 => hone s hs (by
    rw [show s = 0 by exact_mod_cast h0]; exact P.zero_mem)
  obtain ⟨m, hm, hmx⟩ : ∃ m ∈ J * J.map σ,
      algebraMap (𝓞 E) E m = (x : E) * algebraMap (𝓞 E) E (i * σ i) := by
    rw [← FractionalIdeal.mem_coeIdeal (𝓞 E)⁰, ← h, FractionalIdeal.mem_singleton_mul]
    exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2
      ⟨_, Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem _ hi), rfl⟩, rfl⟩
  obtain ⟨m', hm', hmx'⟩ : ∃ m' ∈ I * I.map σ,
      algebraMap (𝓞 E) E (j * σ j) = (x : E) * algebraMap (𝓞 E) E m' := by
    have : algebraMap (𝓞 E) E (j * σ j)
        ∈ ((J * J.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
      (FractionalIdeal.mem_coeIdeal _).2
        ⟨_, Ideal.mul_mem_mul hj (Ideal.mem_map_of_mem _ hj), rfl⟩
    rw [← h, FractionalIdeal.mem_singleton_mul] at this
    obtain ⟨y, hy, hy'⟩ := this
    obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨m', hm', hy'⟩
  obtain ⟨c, hc⟩ := exists_mul_eq_of_mem_mul_map σ hsj hm
  obtain ⟨c', hc'⟩ := exists_mul_eq_of_mem_mul_map σ hri hm'
  have hcE := congrArg (algebraMap (𝓞 E) E) hc
  have hcE' := congrArg (algebraMap (𝓞 E) E) hc'
  have hσE : ∀ a, algebraMap (𝓞 E) E (σ a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := hσ
  simp only [map_mul, hσE] at hcE hcE' hmx hmx'
  rw [hmx] at hcE
  have hj1 : algebraMap (𝓞 E) E j * IsCMField.complexConj E (algebraMap (𝓞 E) E j) ≠ 0 :=
    mul_ne_zero hj0 ((map_ne_zero _).2 hj0)
  have hi1 : algebraMap (𝓞 E) E i * IsCMField.complexConj E (algebraMap (𝓞 E) E i) ≠ 0 :=
    mul_ne_zero hi0 ((map_ne_zero _).2 hi0)
  have hcc : c * c' = (r * σ r) * (s * σ s) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    simp only [map_mul, hσE]
    apply mul_right_cancel₀ hj1
    linear_combination algebraMap (𝓞 E) E c' * hcE
      + algebraMap (𝓞 E) E s * IsCMField.complexConj E (algebraMap (𝓞 E) E s) * (x : E) * hcE'
      - algebraMap (𝓞 E) E s * IsCMField.complexConj E (algebraMap (𝓞 E) E s)
        * algebraMap (𝓞 E) E r * IsCMField.complexConj E (algebraMap (𝓞 E) E r) * hmx'
  have hcP : c ∉ P := fun hcP =>
    (hP.isPrime.mem_or_mem (hcc ▸ P.mul_mem_right c' hcP)).elim (hnorm r hr) (hnorm s hs)
  have hfix : IsCMField.ringOfIntegersComplexConj E c = c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← hσ', hσE]
    have := congrArg (IsCMField.complexConj E) hcE
    simp only [map_mul, IsCMField.complexConj_apply_apply,
      IsCMField.complexConj_apply_eq_self] at this
    apply mul_right_cancel₀ hj1
    linear_combination this - hcE
  obtain ⟨u, rfl⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E c).1 hfix
  refine ⟨algebraMap (𝓞 E) E i * algebraMap (𝓞 E) E s, algebraMap (𝓞 E) E j, u,
    mul_ne_zero hi0 hs0, fun hu => hcP (hQP (Ideal.mem_map_of_mem _ hu)), ?_⟩
  have hu : ((u : maximalRealSubfield E) : E)
      = algebraMap (𝓞 E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) u) := rfl
  rw [hu, map_mul]
  linear_combination -hcE

theorem exists_eq_sq_add_of_notMem (H : Host E)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {u : 𝓞 (maximalRealSubfield E)} (hu : u ∉ v.asIdeal) :
    ∃ a b : v.adicCompletion (maximalRealSubfield E),
      algebraMap (maximalRealSubfield E) _ (u : maximalRealSubfield E) = a ^ 2 + H.d * b ^ 2 := by
  haveI := v.isMaximal
  haveI := H.unram
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal
    (by simp [RingHom.ker_eq_bot_iff_eq_zero, (RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))])
  obtain ⟨w, hw⟩ := exists_sub_notMem
    (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E)
    ⟨H.rt, fun h => by
      have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := congrArg (algebraMap (𝓞 E) E) h
      rw [complexConj_rt, neg_eq_self] at h1
      have h2 : H.rt = 0 := by exact_mod_cast h1
      have h3 := H.rt_sq
      rw [h2, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h3
      exact H.d_prime.ne_zero h3⟩ P hP.ne_top
  have hcc : ∀ y, IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E y)
      = y := fun y => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (y : E))
  obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (w + IsCMField.ringOfIntegersComplexConj E w)).1 (by rw [map_add, hcc, add_comm])
  obtain ⟨n, hn⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (w * IsCMField.ringOfIntegersComplexConj E w)).1 (by rw [map_mul, hcc, mul_comm])
  have hD : a ^ 2 - 4 * n ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap]
    intro h
    apply hw
    apply hP.isPrime.mem_of_pow_mem 2
    convert h using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ha, hn, AlgEquiv.coe_algHom]
    ring
  obtain ⟨r, s, hrs⟩ := exists_binary_eq_adicCompletion v hD hu
  obtain ⟨α, β, hα, hβ⟩ := exists_coords H (w : E)
  have ha' : (a : maximalRealSubfield E) = 2 * α :=
    Subtype.ext ((congrArg (algebraMap (𝓞 E) E) ha).trans hα.symm)
  have hn' : (n : maximalRealSubfield E) = α ^ 2 + H.d * β ^ 2 :=
    Subtype.ext ((congrArg (algebraMap (𝓞 E) E) hn).trans hβ.symm)
  rw [ha', hn'] at hrs
  simp only [map_add, map_mul, map_pow, map_ofNat, map_natCast] at hrs
  refine ⟨r + algebraMap (maximalRealSubfield E) _ α * s,
    algebraMap (maximalRealSubfield E) _ β * s, ?_⟩
  linear_combination -hrs

end GlobalTheory.LocalNorm

namespace GlobalTheory

open LocalNorm in

theorem local_norm_of_ideal_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (x : maximalRealSubfield E), x ≠ 0 → (∃ I J : Ideal (𝓞 E), I ≠ ⊥ ∧ J ≠ ⊥ ∧ FractionalIdeal.spanSingleton (𝓞 E)⁰ ((x : E)) * ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = ((J * J.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ a b : v.adicCompletion (maximalRealSubfield E), algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) x = a ^ 2 - algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (-(H.d : maximalRealSubfield E)) * b ^ 2) := by
  rintro E _ _ _ H x hx ⟨I, J, hI, hJ, h⟩ v
  obtain ⟨z₁, z₂, u, hz, hu, hxu⟩ := exists_mul_norm_eq x hx hI hJ _ H.bar_eq h v
  obtain ⟨a₀, b₀, h₀⟩ := exists_eq_sq_add_of_notMem H v hu
  obtain ⟨a₁, b₁, -, h₁⟩ := exists_coords H z₁
  obtain ⟨a₂, b₂, -, h₂⟩ := exists_coords H z₂
  have hne : a₁ ^ 2 + H.d * b₁ ^ 2 ≠ 0 := fun h0 => by
    rw [h0] at h₁
    exact mul_ne_zero hz ((map_ne_zero _).2 hz) h₁.symm
  have hF : x * (a₁ ^ 2 + H.d * b₁ ^ 2) = u * (a₂ ^ 2 + H.d * b₂ ^ 2) := by
    rw [← h₁, ← h₂] at hxu
    exact Subtype.ext hxu
  have hv := congrArg (algebraMap _ (v.adicCompletion (maximalRealSubfield E))) hF
  have hne' := (map_ne_zero (algebraMap _ (v.adicCompletion (maximalRealSubfield E)))).2 hne
  simp only [map_add, map_mul, map_pow, map_natCast, h₀] at hv hne'
  obtain ⟨a, b, hab⟩ := exists_eq_sq_add_of_mul_eq hne' hv
  exact ⟨a, b, by rw [hab, map_neg, map_natCast]; ring⟩

end GlobalTheory
