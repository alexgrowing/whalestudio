import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

noncomputable section

open NumberField IsDedekindDomain
open scoped WithZero

namespace GlobalTheory.CMVal.ValEx

section Local

variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)

def cong (n : ℕ) : Subgroup Kˣ where
  carrier := {x | v (x : K) = 1 ∧ v ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul, map_mul, ha.1, hb.1, one_mul], by
    have : ((a * b : Kˣ) : K) - 1 = a * ((b : K) - 1) + ((a : K) - 1) := by rw [Units.val_mul]; ring
    rw [this]
    exact v.map_add_le (by rw [map_mul, ha.1, one_mul]; exact hb.2) ha.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [Units.val_inv_eq_inv_val, map_inv₀, ha.1, inv_one], by
    have : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K)⁻¹ * ((a : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, v.map_neg, map_mul, map_inv₀, ha.1, inv_one, one_mul]; exact ha.2⟩

theorem cong_anti {m n : ℕ} (h : m ≤ n) : cong v n ≤ cong v m := fun _ hx =>
  ⟨hx.1, hx.2.trans (WithZero.exp_le_exp.2 (by omega))⟩

theorem val_nat_le (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => push_cast; exact v.map_add_le ih (by simp)

theorem val_int_le (n : ℤ) : v (n : K) ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_nat_le v m
  · simpa using val_nat_le v m

theorem val_binom {t : K} (ht : v t ≤ 1) (n : ℕ) : v ((1 + t) ^ n - 1 - n * t) ≤ v t * v t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (1 + t) ^ (n + 1) - 1 - ((n + 1 : ℕ) : K) * t = (1 + t) * ((1 + t) ^ n - 1 - n * t) + n * (t * t) := by
      push_cast; ring
    rw [this]
    refine v.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_mul' (v.map_add_le (by simp) ht) ih).trans (by rw [one_mul])
    · rw [map_mul, map_mul]
      exact (mul_le_mul' (val_nat_le v n) le_rfl).trans (by rw [one_mul])

theorem exp_one_sq : WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) = WithZero.exp (-2 : ℤ) := by
  rw [← WithZero.exp_add]; norm_num

theorem exp_one_le : WithZero.exp (-1 : ℤ) ≤ (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num

theorem eq_one_of_cong {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hv : v (l : K) = WithZero.exp (-1 : ℤ)) {z : Kˣ}
    (hz : IsOfFinOrder z) (h1 : z ∈ cong v 1) : z = 1 := by
  by_contra hne
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (n := orderOf z) (fun h => hne (orderOf_eq_one_iff.1 h))
  have hpos := hz.orderOf_pos
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hη : z ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 (by
    rw [hk]; have := hp.two_le; nlinarith [Nat.pos_of_ne_zero hk0])
  have hηp : (z ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  have hc := (cong v 1).pow_mem h1 k
  generalize z ^ k = y at hη hηp hc
  obtain ⟨t, ht⟩ : ∃ t : K, (y : K) = 1 + t := ⟨y - 1, by ring⟩
  have ht0 : t ≠ 0 := by rintro rfl; exact hη (Units.ext (by simpa using ht))
  have ht1 : v t ≤ WithZero.exp (-1 : ℤ) := by simpa [ht] using hc.2
  have hp1 : (1 + t) ^ p = 1 := by rw [← ht, ← Units.val_pow_eq_pow_val, hηp, Units.val_one]
  have hvp : v (p : K) ≤ WithZero.exp (-1 : ℤ) := by
    have := val_binom v (ht1.trans exp_one_le) p
    rw [hp1, sub_self, zero_sub, v.map_neg, map_mul] at this
    exact (le_of_mul_le_mul_right this (zero_lt_iff.2 (by simpa using ht0))).trans ht1
  have hpl : p = l := by
    by_contra hpl
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
    have e : (1 : K) = (a : K) * p + (b : K) * l := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab.symm
    have : v (1 : K) ≤ WithZero.exp (-1 : ℤ) := by
      rw [e]
      refine v.map_add_le ?_ ?_ <;> rw [map_mul]
      · exact (mul_le_mul' (val_int_le v a) hvp).trans (by rw [one_mul])
      · exact (mul_le_mul' (val_int_le v b) hv.le).trans (by rw [one_mul])
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  subst hpl
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two h2
  have hs : ∑ i ∈ Finset.range p, (1 + t) ^ i = 0 := by
    have := geom_sum_mul (1 + t) p
    rw [hp1, sub_self, add_sub_cancel_left] at this
    exact (mul_eq_zero.1 this).resolve_right ht0
  have hsum : ∑ i ∈ Finset.range p, i = p * m := by
    have := Finset.sum_range_id_mul_two p
    have e : p - 1 = 2 * m := by omega
    rw [e] at this; nlinarith
  have hsum' : ∑ i ∈ Finset.range p, (i : K) = p * m := by
    have := congrArg (Nat.cast : ℕ → K) hsum
    rwa [Nat.cast_sum, Nat.cast_mul] at this
  have e : (p : K) = -(∑ i ∈ Finset.range p, ((1 + t) ^ i - 1 - i * t)) - (m : K) * (p * t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs, ← Finset.sum_mul, hsum']; simp; ring
  have : v (p : K) ≤ WithZero.exp (-2 : ℤ) := by
    rw [e, ← exp_one_sq]
    refine v.map_sub_le ?_ ?_
    · rw [v.map_neg]
      exact v.map_sum_le fun i _ => (val_binom v (ht1.trans exp_one_le) i).trans (mul_le_mul' ht1 ht1)
    · rw [map_mul, map_mul]
      exact (mul_le_mul' (val_nat_le v m) (mul_le_mul' hv.le ht1)).trans (by rw [one_mul])
  rw [hv, WithZero.exp_le_exp] at this
  omega

end Local

open WithZeroTopology in
theorem continuous_of_val {K L : Type} [Field K] [Field L] [Valued K ℤᵐ⁰] [Valued L ℤᵐ⁰]
    (hK : Function.Surjective (Valued.v : K → ℤᵐ⁰)) (f : K →+* L) (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have ho : IsOpen {x : K | Valued.v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} :=
    WithZeroTopology.isOpen_Iio.preimage (Valued.continuous_valuation_of_surjective hK)
  filter_upwards [ho.mem_nhds (by simp [zero_lt_iff])] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]
  exact hx

variable {E : Type} [Field E] [NumberField E]

open WithZeroTopology in
theorem continuous_val (w : HeightOneSpectrum (𝓞 E)) : Continuous fun x : w.adicCompletion E => Valued.v x :=
  Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective E)

open WithZeroTopology in

theorem exists_locMap (σ : E ≃+* E) (w w' : HeightOneSpectrum (𝓞 E)) (h : ∀ y, w'.valuation E y = w.valuation E (σ y)) :
    ∃ c : w'.adicCompletion E →+* w.adicCompletion E, Continuous c ∧
      (∀ y, c (algebraMap E _ y) = algebraMap E _ (σ y)) ∧ ∀ x, Valued.v (c x) = Valued.v x := by
  have hc : Continuous (WithVal.map (w'.valuation E) (w.valuation E) σ.toRingHom) :=
    continuous_of_val (fun γ => by
      obtain ⟨y, hy⟩ := w'.valuation_surjective E γ
      exact ⟨WithVal.toVal _ y, hy⟩) _ (fun x => (h x.ofVal).symm)
  let c : w'.adicCompletion E →+* w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E w).symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv E w').toRingHom
  have hcc : Continuous c := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w'))
  have ha : ∀ y, c (algebraMap E _ y) = algebraMap E _ (σ y) := fun y => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ y)
  refine ⟨c, hcc, ha, fun x => ?_⟩
  refine congrFun ((w'.denseRange_algebraMap E).equalizer ((continuous_val w).comp hcc) (continuous_val w') ?_) x
  funext y
  simp only [Function.comp_apply, ha]
  exact (w.valuedAdicCompletion_eq_valuation' (σ y)).trans ((h y).symm.trans (w'.valuedAdicCompletion_eq_valuation' y).symm)

open WithZeroTopology in
theorem isOpen_cong (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    IsOpen (cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) n : Set (w.adicCompletion E)ˣ) := by
  have h1 : IsOpen ({1} : Set ℤᵐ⁰) := WithZeroTopology.isOpen_iff.2 (Or.inl (by simp))
  have h2 : IsOpen (Set.Iic (WithZero.exp (-(n : ℤ)))) :=
    WithZeroTopology.isOpen_iff.2 (Or.inr ⟨_, WithZero.exp_ne_zero, Set.Iio_subset_Iic_self⟩)
  exact (h1.preimage ((continuous_val w).comp Units.continuous_val)).inter
    (h2.preimage ((continuous_val w).comp (Units.continuous_val.sub continuous_const)))

theorem val_prime {l : ℕ} (hl : l.Prime) (hd : ¬ (l : ℤ) ∣ discr E) (w : HeightOneSpectrum (𝓞 E))
    (hw : (l : 𝓞 E) ∈ w.asIdeal) : w.valuation E (l : E) = WithZero.exp (-1 : ℤ) := by
  have hP := w.isPrime
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd _ hP (by simpa using hw)
  have hov : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hw)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have h1 := Ideal.ramificationIdx_eq_one w.asIdeal ℤ
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne, hmap] at h1
  have e : (l : E) = algebraMap (𝓞 E) E l := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hl0]
  have := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors w.irreducible
    (b := Ideal.span {(l : 𝓞 E)}) (by simpa using hl.ne_zero)
  rw [normalize_eq, h1] at this
  rw [multiplicity_eq_of_emultiplicity_eq_some this]; rfl

def toLoc (w : HeightOneSpectrum (𝓞 E)) : Eˣ →* (w.adicCompletion E)ˣ :=
  Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom

theorem val_alg (w : HeightOneSpectrum (𝓞 E)) (y : E) :
    Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := w.valuedAdicCompletion_eq_valuation' y

theorem exists_locChar {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (w : HeightOneSpectrum (𝓞 E))
    (hv : w.valuation E (l : E) = WithZero.exp (-1 : ℤ)) (θ : Eˣ →* ℂˣ)
    (u : Eˣ) (hu : (u : E) = 1 + l) :
    ∃ ch : (w.adicCompletion E)ˣ →* ℂˣ, Continuous ch ∧ (∀ x, ‖((ch x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ x ∈ cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) 2, ch x = 1) ∧
      (∀ z, IsOfFinOrder z → ch (toLoc w z) = θ z) ∧ ch (toLoc w u) ≠ 1 := by
  have hω := Complex.isPrimitiveRoot_exp l hl.ne_zero
  have hω1 := hω.norm'_eq_one hl.ne_zero
  generalize Complex.exp (2 * Real.pi * Complex.I / l) = ω at hω hω1
  let ω' : ℂˣ := Units.mk0 ω (hω.ne_zero hl.ne_zero)
  have hω' : ω' ^ l = 1 := Units.ext (by simpa [ω'] using hω.pow_eq_one)
  have hmem : ∀ n (k : Eˣ), toLoc w k ∈ cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) n ↔
      k ∈ cong (w.valuation E) n := fun n k => by
    change (Valued.v (algebraMap E (w.adicCompletion E) k) = 1 ∧
      Valued.v (algebraMap E (w.adicCompletion E) k - 1) ≤ _) ↔ _
    rw [← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, val_alg, val_alg]
    rfl
  have hlt : w.valuation E (l : E) < 1 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu1 : u ∈ cong (w.valuation E) 1 := ⟨by rw [hu]; exact Valuation.map_one_add_of_lt _ hlt, by
    rw [hu, add_sub_cancel_left, hv]; simp⟩
  have hu2 : u ∉ cong (w.valuation E) 2 := fun h => by
    have := h.2
    rw [hu, add_sub_cancel_left, hv, WithZero.exp_le_exp] at this
    omega
  have hul : u ^ l ∈ cong (w.valuation E) 2 := ⟨((cong _ 1).pow_mem hu1 l).1, by
    have e : ((u ^ l : Eˣ) : E) - 1 = ((1 + (l : E)) ^ l - 1 - l * l) + l * l := by
      rw [Units.val_pow_eq_pow_val, hu]; ring
    have e2 : w.valuation E (l : E) * w.valuation E (l : E) = WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [hv, exp_one_sq]; rfl
    rw [e, ← e2]
    exact Valuation.map_add_le _ (val_binom _ hlt.le l) (map_mul _ _ _).le⟩
  haveI := Fact.mk hl
  have hord : orderOf (QuotientGroup.mk' (cong (w.valuation E) 2) u) = l :=
    orderOf_eq_prime (by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hul)
      (fun h => hu2 ((QuotientGroup.eq_one_iff _).1 h))
  obtain ⟨ch, h1, h3, h4, h5⟩ := exists_unitary_char_of_open_subgroup_and_hom _
    (CommGroup.torsion Eˣ × Multiplicative ℤ) _ (isOpen_cong w 2)
    ((toLoc w).comp ((CommGroup.torsion Eˣ).subtype.coprod (zpowersHom _ u)))
    ((θ.comp (CommGroup.torsion Eˣ).subtype).coprod (zpowersHom _ ω')) 1 continuous_const (by simp)
    (fun y => by
      have hθ : ‖((θ y.1 : ℂˣ) : ℂ)‖ = 1 := (((Units.coeHom ℂ).comp θ).isOfFinOrder y.1.2).norm_eq_one
      simp [hθ, ω', hω1]) (fun y hy => by
      have hy' : (y.1 : Eˣ) * u ^ y.2.toAdd ∈ cong (w.valuation E) 2 := (hmem 2 _).1 hy
      have hz : (y.1 : Eˣ) = 1 := eq_one_of_cong _ hl h2 hv y.1.2
        ((Subgroup.mul_mem_cancel_right _ ((cong _ 1).zpow_mem hu1 _)).1 (cong_anti _ (by norm_num) hy'))
      rw [hz, one_mul, ← QuotientGroup.eq_one_iff] at hy'
      have hd : ((orderOf (QuotientGroup.mk' (cong (w.valuation E) 2) u) : ℕ) : ℤ) ∣ y.2.toAdd :=
        orderOf_dvd_iff_zpow_eq_one.2 (by rw [← map_zpow]; exact hy')
      rw [hord] at hd
      obtain ⟨m, hm⟩ := hd
      change θ (y.1 : Eˣ) * ω' ^ y.2.toAdd = 1
      rw [hz, hm, zpow_mul, zpow_natCast, hω']; simp)
  refine ⟨ch, h1, h3, h4, fun z hz => ?_, ?_⟩
  · simpa using h5 (⟨z, hz⟩, 1)
  · have := h5 (1, Multiplicative.ofAdd 1)
    simp only [MonoidHom.comp_apply, MonoidHom.coprod_apply, map_one, one_mul, zpowersHom_apply, toAdd_ofAdd, zpow_one] at this
    rw [this]
    exact fun h => hω.ne_one hl.one_lt (congrArg Units.val h)

theorem exists_infExt (φ : E →+* ℂ) :
    ∃ e : InfiniteAdeleRing E →+* ℂ, Continuous e ∧ (∀ k : E, e (algebraMap E _ k) = φ k) ∧
      ∀ x y : InfiniteAdeleRing E, x (InfinitePlace.mk φ) = y (InfinitePlace.mk φ) → e x = e y := by
  have h0 : ∀ k : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap E _ k) =
      (InfinitePlace.mk φ).embedding k := fun k =>
    InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  let e : InfiniteAdeleRing E →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)).comp (Pi.evalRingHom _ (InfinitePlace.mk φ))
  have he : Continuous e := hc.comp (continuous_apply _)
  have h1 : ∀ k, e (algebraMap E _ k) = (InfinitePlace.mk φ).embedding k := h0
  have h2 : ∀ x y : InfiniteAdeleRing E, x (InfinitePlace.mk φ) = y (InfinitePlace.mk φ) → e x = e y := fun x y h =>
    congrArg (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)) h
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨e, he, fun k => by rw [h1, h], h2⟩
  · refine ⟨(starRingEnd ℂ).comp e, Complex.continuous_conj.comp he, fun k => ?_,
      fun x y h => congrArg (starRingEnd ℂ) (h2 x y h)⟩
    rw [RingHom.comp_apply, h1, h]
    simp

theorem exists_infChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) :
    ∃ ψ : (InfiniteAdeleRing E)ˣ →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ k : Eˣ, ((ψ (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) : ℂˣ) : ℂ) =
        ∏ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i) ∧
      ∀ k : E, k ∈ maximalRealSubfield E → ∀ x : (InfiniteAdeleRing E)ˣ,
        (∀ w, x.1 w = (1 : InfiniteAdeleRing E) w ∨ x.1 w = algebraMap E (InfiniteAdeleRing E) k w) → ψ x = 1 := by
  choose e he he' he2 using fun i => exists_infExt (φ i)
  let ψ : (InfiniteAdeleRing E)ˣ →* ℂˣ :=
    ∏ i, (Units.map (e i).toMonoidHom / Units.map ((starRingEnd ℂ).comp (e i)).toMonoidHom) ^ m i
  have h0 : ∀ x, ψ x = ∏ i, (Units.map (e i).toMonoidHom x / Units.map ((starRingEnd ℂ).comp (e i)).toMonoidHom x) ^ m i :=
    fun x => by simp only [ψ, MonoidHom.finsetProd_apply]; rfl
  have h1 : ∀ x, (ψ x : ℂ) = ∏ i, (e i x / starRingEnd ℂ (e i x)) ^ m i := fun x => by
    rw [h0]; simp
  refine ⟨ψ, ?_, fun x => ?_, fun k => ?_, fun k hk x hx => Units.ext ?_⟩
  · rw [show (ψ : _ → _) = _ from funext h0]
    exact continuous_finsetProd _ fun i _ =>
      ((Continuous.units_map _ (he i)).div' (Continuous.units_map _ (Complex.continuous_conj.comp (he i)))).zpow _
  · rw [h1, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have : e i x ≠ 0 := (x.isUnit.map (e i)).ne_zero
    rw [norm_zpow, norm_div, Complex.norm_conj, div_self (by simpa using this), one_zpow]
  · rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← he']; rfl
  · rw [h1]
    refine Finset.prod_eq_one fun i _ => ?_
    have h2 : e i x ≠ 0 := (x.isUnit.map (e i)).ne_zero
    have h3 : starRingEnd ℂ (e i x) = e i x := by
      rcases hx (InfinitePlace.mk (φ i)) with h | h
      · rw [he2 i _ _ h, map_one, map_one]
      · rw [he2 i _ _ h, he']; exact hk (φ i)
    rw [h3, div_self h2, one_zpow]

section CM

variable [IsCMField E]

local notation "cc" => IsCMField.complexConj E

def bar (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  w.comap (RingOfIntegers.mapRingEquiv (cc).toRingEquiv : 𝓞 E →+* 𝓞 E) (RingOfIntegers.mapRingEquiv (cc).toRingEquiv).surjective

theorem val_bar (w : HeightOneSpectrum (𝓞 E)) (y : E) : (bar w).valuation E y = w.valuation E ((cc).toRingEquiv y) :=
  GlobalTheory.QNorm.valuation_of_eq_comap _ w _ rfl y

theorem over_bar {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) : Over (bar w) v := by
  unfold Over at h ⊢
  rw [← h]
  ext y
  have : RingOfIntegers.mapRingEquiv (cc).toRingEquiv (algebraMap (OF E) (𝓞 E) y) = algebraMap (OF E) (𝓞 E) y :=
    RingOfIntegers.ext ((cc).commutes (y : maximalRealSubfield E))
  change RingOfIntegers.mapRingEquiv (cc).toRingEquiv (algebraMap (OF E) (𝓞 E) y) ∈ w.asIdeal ↔
    algebraMap (OF E) (𝓞 E) y ∈ w.asIdeal
  rw [this]

theorem eq_or_eq_bar {w P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) (hP : Over P v) :
    P = w ∨ P = bar w := by
  have hsub : (P.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (bar w).asIdeal := fun x hx => by
    let y : 𝓞 E := x * RingOfIntegers.mapRingEquiv (cc).toRingEquiv x
    have hy : (y : E) ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff]
      change cc ((x : E) * cc (x : E)) = (x : E) * cc (x : E)
      rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hint : IsIntegral ℤ (⟨y, hy⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 y.isIntegral_coe
    obtain ⟨a, hn⟩ : ∃ a : OF E, algebraMap (OF E) (𝓞 E) a = y := ⟨⟨_, hint⟩, RingOfIntegers.ext rfl⟩
    have h1 : a ∈ v.asIdeal := by
      rw [← hP, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h, Ideal.mem_comap, hn] at h1
    exact w.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · exact Or.inl (HeightOneSpectrum.ext (P.isMaximal.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (bar w).isPrime.ne_top h))

theorem isOfFinOrder_div (k : Eˣ) (h : ∀ w : HeightOneSpectrum (𝓞 E), (bar w).valuation E k = w.valuation E k) :
    IsOfFinOrder (k / Units.map (cc).toRingEquiv.toMonoidHom k) := by
  have e : ((k / Units.map (cc).toRingEquiv.toMonoidHom k : Eˣ) : E) = (k : E) / cc (k : E) := by simp
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k : E) / cc (k : E)) fun w => by
    have := h w
    rw [val_bar] at this
    rw [map_div₀, ← this]
    exact div_self_le_one _
  obtain ⟨n, hn, h1⟩ := Embeddings.pow_eq_one_of_norm_eq_one E ℂ (x := (k : E) / cc (k : E)) (ha ▸ a.isIntegral_coe) fun σ => by
    rw [map_div₀, IsCMField.complexEmbedding_complexConj, norm_div, Complex.norm_conj, div_self (by simp)]
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val, e, h1, Units.val_one])⟩

end CM

def locU (P : HeightOneSpectrum (𝓞 E)) : (Af E)ˣ →* (P.adicCompletion E)ˣ :=
  Units.map { toFun := fun x : Af E => x P, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem continuous_locU (P : HeightOneSpectrum (𝓞 E)) : Continuous (locU P) :=
  Continuous.units_map _ (RestrictedProduct.continuous_eval P)

def finOf : Ideles E →* (Af E)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing E) (Af E))

def infOf : Ideles E →* (InfiniteAdeleRing E)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing E) (Af E))

theorem continuous_finOf : Continuous (finOf (E := E)) := Continuous.units_map _ continuous_snd

theorem continuous_infOf : Continuous (infOf (E := E)) := Continuous.units_map _ continuous_fst

def unitI : Subgroup (Ideles E) :=
  ⨅ P : HeightOneSpectrum (𝓞 E), (cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) 0).comap ((locU P).comp finOf)

theorem mem_unitI {x : Ideles E} : x ∈ unitI ↔ ∀ P, Valued.v ((finOf x : Af E) P) = 1 := by
  simp only [unitI, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall_congr' fun P => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact Valuation.map_sub_le _ h.le (by simp)

theorem isOpen_unitI : IsOpen (unitI (E := E) : Set (Ideles E)) := by
  have hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  convert (hO.preimage (Units.continuous_val.comp continuous_finOf)).inter
    (hO.preimage (Units.continuous_val.comp (continuous_finOf.comp continuous_inv))) using 1
  ext x
  constructor
  · intro h
    exact ⟨fun P => (mem_unitI.1 h P).le, fun P => (mem_unitI.1 (unitI.inv_mem h) P).le⟩
  · rintro ⟨h1, h2⟩
    refine mem_unitI.2 fun P => le_antisymm (h1 P) ?_
    have h3 : Valued.v (((locU P (finOf x⁻¹) : (P.adicCompletion E)ˣ)) : P.adicCompletion E) ≤ 1 := h2 P
    rw [map_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h3
    exact (inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (locU P (finOf x)).ne_zero))).1 h3

theorem locU_of_supp {P w : HeightOneSpectrum (𝓞 E)} {y : (Af E)ˣ} (h : SuppAt P y) (hw : w ≠ P) : locU w y = 1 :=
  Units.ext (h w hw)

theorem finIdele_mem {P : HeightOneSpectrum (𝓞 E)} {y : (Af E)ˣ} (h : SuppAt P y) (h1 : Valued.v ((y : Af E) P) = 1) :
    finIdele E y ∈ unitI := mem_unitI.2 fun w => by
  change Valued.v ((y : Af E) w) = 1
  by_cases hw : w = P
  · rw [hw, h1]
  · rw [h w hw, map_one]

theorem expAt_two {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h2 : LevelLe χ P 2) (h1 : ¬ LevelLe χ P 1) : ExpAt χ P 2 :=
  fun m => ⟨fun h => by
    by_contra hm
    exact h1 fun y a b => h y a (b.trans (WithZero.exp_le_exp.2 (by omega))),
    fun hm y a b => h2 y a (b.trans (WithZero.exp_le_exp.2 (by omega)))⟩

theorem locU_single (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) : locU P (single P x) = x :=
  Units.ext (single_self P x)

open Classical in
theorem locU_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (k : Eˣ) (Q : HeightOneSpectrum (𝓞 E)) :
    locU Q (∏ P ∈ S, single P (toLoc P k)) = if Q ∈ S then toLoc Q k else 1 := by
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem Q h fun P _ hP => locU_of_supp (suppAt_single P _) hP.symm, locU_single]
  · exact Finset.prod_eq_one fun P hP => locU_of_supp (suppAt_single P _) (fun e => h (e ▸ hP))

theorem exists_isValChar (E : Type) [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (_hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (v : HeightOneSpectrum (OF E)) (hv : IsBaseCond (v.asIdeal ^ 2)) :
    ∃ χ : HChar E, IsValChar φ s κ (v.asIdeal ^ 2) ∅ χ := by
  classical
  obtain ⟨⟨w, w', hne, hw, hw'⟩, -, l, hl, h2, hlv, hd, -⟩ := hv.2.2 v (dvd_pow_self _ two_ne_zero)
  have hbw : bar w ≠ w := fun h => (eq_or_eq_bar hw hw').elim (fun e => hne e.symm) (fun e => hne (e.trans h).symm)
  have hval : ∀ P, Over P v → P.valuation E (l : E) = WithZero.exp (-1 : ℤ) := fun P hP => val_prime hl hd P (by
    rw [← hP, Ideal.mem_comap, map_natCast] at hlv; exact hlv)
  obtain ⟨ψi, hi1, hi2, hi3, hi4⟩ := exists_infChar φ (fun i => (κ i : ℤ) + s)
  let u : Eˣ := Units.mk0 (1 + l) (by exact_mod_cast (by omega : 1 + l ≠ 0))
  obtain ⟨ch, hc1, hc2, hc3, hc4, hc5⟩ := exists_locChar hl h2 w (hval w hw)
    (∏ i, Units.map (φ i).toMonoidHom ^ ((κ i : ℤ) + s))⁻¹ u rfl
  choose c hcc hca hcv using fun P : HeightOneSpectrum (𝓞 E) =>
    exists_locMap (IsCMField.complexConj E).toRingEquiv P (bar P) (val_bar P)
  have hcF : ∀ P (k : Eˣ), (k : E) ∈ maximalRealSubfield E →
      Units.map (c P).toMonoidHom (toLoc (bar P) k) = toLoc P k := fun P k hk =>
    Units.ext ((hca P k).trans (congrArg _ ((IsCMField.complexConj_eq_self_iff E (k : E)).2 hk)))
  let Fx : Subgroup (Af E)ˣ := ⨅ P, ((Units.map (c P).toMonoidHom).comp (locU (bar P))).eqLocus (locU P)
  have hFx : ∀ y, y ∈ Fx ↔ ∀ P, Units.map (c P).toMonoidHom (locU (bar P) y) = locU P y := fun y => Subgroup.mem_iInf
  let ρ : (Af E)ˣ →* (w.adicCompletion E)ˣ := locU w / (Units.map (c w).toMonoidHom).comp (locU (bar w))
  have hρ : ∀ y, ρ y = locU w y / Units.map (c w).toMonoidHom (locU (bar w) y) := fun _ => rfl
  let ψ : Ideles E →* ℂˣ := ψi.comp infOf * ch.comp (ρ.comp finOf)
  have hψ : ∀ x, ψ x = ψi (infOf x) * ch (ρ (finOf x)) := fun _ => rfl
  have hρF : ∀ y ∈ Fx, ρ y = 1 := fun y hy => by rw [hρ, (hFx y).1 hy w, div_self']
  obtain ⟨χ, h1, h3, h4, h5⟩ := exists_unitary_char_of_open_subgroup_and_hom (Ideles E)
    (Eˣ × Fx) unitI isOpen_unitI
    ((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) 1 ψ
    ((hi1.comp continuous_infOf).mul (hc1.comp (((continuous_locU w).div'
      ((Continuous.units_map _ (hcc w)).comp (continuous_locU (bar w)))).comp continuous_finOf)))
    (fun x => by rw [hψ, Units.val_mul, norm_mul, hi2, hc2, one_mul]) (by simp) (by
      rintro ⟨k, y⟩ hy
      have hk : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E k * Valued.v (locU P y.1 : P.adicCompletion E) = 1 := fun P => by
        rw [← val_alg, ← map_mul]; exact mem_unitI.1 hy P
      have hfin := isOfFinOrder_div k fun P => by
        have e1 := hk P
        have e2 := hk (bar P)
        have e3 : c P (locU (bar P) y.1 : (bar P).adicCompletion E) = locU P y.1 := congrArg Units.val ((hFx _).1 y.2 P)
        rw [← hcv, e3] at e2
        exact (eq_inv_of_mul_eq_one_left e2).trans (eq_inv_of_mul_eq_one_left e1).symm
      have e1 : infOf (((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) (k, y)) =
          Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k := Units.ext (mul_one _)
      have e2 : finOf (((Neutral.B1.diagUnits E).coprod ((finIdele E).comp (Subgroup.subtype _))) (k, y)) =
          Units.map (algebraMap E (Af E)).toMonoidHom k * y.1 := Units.ext rfl
      have e3 : ρ (Units.map (algebraMap E (Af E)).toMonoidHom k) =
          toLoc w (k / Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k) := by
        rw [hρ, map_div]
        congr 1
        exact Units.ext (hca w k)
      rw [hψ, e1, e2, map_mul, hρF _ y.2, mul_one, e3, hc4 _ hfin]
      rw [MonoidHom.inv_apply, MonoidHom.one_apply, eq_comm, mul_inv_eq_one, MonoidHom.finsetProd_apply]
      apply Units.ext
      rw [hi3, Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← IsCMField.complexEmbedding_complexConj]
      simp)
  let X : HChar E := ⟨χ, h1, fun k => by simpa using h5 (k, 1)⟩
  have hloc : ∀ P (x : (P.adicCompletion E)ˣ), Valued.v (x : P.adicCompletion E) = 1 → X.loc P x = ch (ρ (single P x)) := by
    intro P x hx
    have e1 : infOf (finIdele E (single P x)) = 1 := Units.ext rfl
    have e2 : finOf (finIdele E (single P x)) = single P x := Units.ext rfl
    change χ (finIdele E (single P x)) = _
    rw [h4 _ (finIdele_mem (suppAt_single P x) (by rw [single_self, hx])), hψ, e1, e2, map_one, one_mul]
  have hinf : ∀ x : Ideles E, finOf x = 1 → χ x = ψi (infOf x) := fun x hx => by
    rw [h4 _ (mem_unitI.2 fun P => by rw [hx]; exact map_one _), hψ, hx, map_one, map_one, mul_one]
  have hu1 : ∀ P, Over P v → toLoc P u ∈ cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) 1 := fun P hP => by
    have e : (toLoc P u : P.adicCompletion E) = 1 + algebraMap E _ (l : E) := by
      change algebraMap E _ (1 + (l : E)) = _
      rw [map_add, map_one]
    refine ⟨?_, ?_⟩ <;> rw [e]
    · refine Valuation.map_one_add_of_lt _ ?_
      rw [val_alg, hval P hP, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · rw [add_sub_cancel_left, val_alg, hval P hP]; simp
  refine ⟨X, h3, ⟨fun q k => ?_, fun q k => ?_⟩, (hasInfRatio_iff _ _ _).2 fun k => ?_, fun q P hP => ⟨by simp, fun _ => ?_⟩⟩
  · have hm : ∀ Q, Q ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) q ↔ Over Q q := fun Q => by
      unfold Formalism.L2.Host.aboveF
      rw [Set.Finite.mem_toFinset]
      exact HeightOneSpectrum.ext_iff
    have hy : ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) q,
        single P (toLoc P (Formalism.L2.Host.upF (maximalRealSubfield E) k)) ∈ Fx := (hFx _).2 fun Q => by
      rw [locU_prod, locU_prod]
      by_cases hQ : Over Q q
      · rw [if_pos ((hm _).2 hQ), if_pos ((hm _).2 (over_bar hQ))]
        exact hcF Q _ (k : maximalRealSubfield E).2
      · rw [if_neg (fun h => hQ ((hm _).1 h)), if_neg, map_one]
        intro h
        have e : Over (bar Q) (Q.under (OF E)) := over_bar rfl
        exact hQ (Eq.trans (Eq.symm e) ((hm _).1 h))
    have := h5 (1, ⟨_, hy⟩)
    simp only [MonoidHom.coprod_apply, map_one, one_mul, MonoidHom.comp_apply, Subgroup.subtype_apply, map_prod,
      MonoidHom.one_apply] at this
    unfold Formalism.L2.Host.HChar.resFin
    rw [MonoidHom.finsetProd_apply]
    exact this
  · unfold Formalism.L2.Host.HChar.resInf
    rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun t _ => ?_
    refine (hinf _ (Units.ext rfl)).trans (hi4 _ (k : maximalRealSubfield E).2 _ fun t' => ?_)
    by_cases h : t' = t
    · subst h
      exact Or.inr (Pi.mulSingle_eq_same (M := fun w : InfinitePlace E => w.Completion) _ _)
    · exact Or.inl (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace E => w.Completion) h _)
  · rw [← hi3]
    change ((χ (infDiag k) : ℂˣ) : ℂ) = _
    rw [infDiag_eq]
    exact congrArg Units.val (hinf _ (Units.ext rfl))
  · by_cases hq : q = v
    · subst hq
      have e : expIn (q.asIdeal ^ 2) q = 2 :=
        multiplicity_pow_self q.ne_bot (fun h => q.isPrime.ne_top (Ideal.isUnit_iff.1 h)) 2
      rw [e]
      rcases eq_or_eq_bar hw hP with rfl | rfl
      · have e2 : ∀ x, ρ (single P x) = x := fun x => by
          rw [hρ, locU_single, locU_of_supp (suppAt_single P x) hbw, map_one, div_one]
        refine expAt_two (fun x h h' => ?_) (fun h => hc5 ?_)
        · rw [hloc P x h, e2]; exact hc3 x ⟨h, h'⟩
        · rw [← e2 (toLoc P u), ← hloc P _ (hu1 P hP).1]; exact h _ (hu1 P hP).1 (hu1 P hP).2
      · have e2 : ∀ x, ρ (single (bar w) x) = (Units.map (c w).toMonoidHom x)⁻¹ := fun x => by
          rw [hρ, locU_single, locU_of_supp (suppAt_single _ x) hbw.symm, one_div]
        refine expAt_two (fun x h h' => ?_) (fun h => hc5 ?_)
        · rw [hloc _ x h, e2, map_inv, inv_eq_one]
          refine hc3 _ ⟨(hcv w _).trans h, ?_⟩
          rw [← hcv w, map_sub, map_one] at h'
          exact h'
        · have := h _ (hu1 _ hP).1 (hu1 _ hP).2
          rwa [hloc _ _ (hu1 _ hP).1, e2, map_inv, inv_eq_one, hcF w u (add_mem (one_mem _) (natCast_mem _ l))] at this
    · have e : expIn (v.asIdeal ^ 2) q = 0 := multiplicity_eq_zero.2 fun h => hq
        (HeightOneSpectrum.ext (v.isMaximal.eq_of_le q.isPrime.ne_top
          (Ideal.dvd_iff_le.1 (q.prime.dvd_of_dvd_pow h))).symm)
      have hn : ∀ Q, Over Q v → Q ≠ P := fun Q hQ h => hq (HeightOneSpectrum.ext (Eq.trans (Eq.symm hP) (h ▸ hQ)))
      rw [e, expAt_zero_iff]
      intro x hx
      rw [hloc P x hx, hρ, locU_of_supp (suppAt_single P x) (hn w hw), locU_of_supp (suppAt_single P x) (hn _ (over_bar hw))]
      simp

end GlobalTheory.CMVal.ValEx
