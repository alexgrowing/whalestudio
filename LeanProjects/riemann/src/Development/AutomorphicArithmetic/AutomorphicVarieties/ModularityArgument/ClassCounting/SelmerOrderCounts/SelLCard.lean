import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

open scoped nonZeroDivisors

private theorem ord_eq_count {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (y : Lˣ) :
    ordP p y = FractionalIdeal.count L p (FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L)) := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (𝓞 L)⁰ (y : L)
  have ha : a ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hab, IsLocalization.mk'_zero])
  have hb : (b : 𝓞 L) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hI : FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero
  have h : FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L) =
      FractionalIdeal.spanSingleton (𝓞 L)⁰ ((algebraMap (𝓞 L) L) b)⁻¹ * ((Ideal.span {a} : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, ← hab,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined L p hI h, ordP, ← hab, HeightOneSpectrum.valuation_of_mk',
    p.intValuation_if_neg ha, p.intValuation_if_neg hb, ← WithZero.exp_sub, WithZero.log_exp]
  ring

private theorem ord_mul {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (x y : Lˣ) :
    ordP p (x * y) = ordP p x + ordP p y := by
  rw [ord_eq_count, ord_eq_count, ord_eq_count, Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L p (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero)]

private theorem ord_one {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) :
    ordP p (1 : Lˣ) = 0 := by
  have := ord_mul p (1 : Lˣ) 1
  rw [mul_one] at this
  omega

private theorem ord_inv {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    ordP p x⁻¹ = -ordP p x := by
  have := ord_mul p x x⁻¹
  rw [mul_inv_cancel, ord_one] at this
  omega

private theorem fi_ext {L : Type} [Field L] [NumberField L] {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ p, FractionalIdeal.count L p I = FractionalIdeal.count L p J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' L hJ]
  exact finprod_congr fun p => by rw [h p]

private theorem root_unique {L : Type} [Field L] [NumberField L] {l : ℕ} (hl : l ≠ 0)
    {I J : (FractionalIdeal (𝓞 L)⁰ L)ˣ} (h : I ^ l = J ^ l) : I = J := by
  refine Units.ext (fi_ext I.ne_zero J.ne_zero fun p => ?_)
  have h1 := congrArg (fun X : (FractionalIdeal (𝓞 L)⁰ L)ˣ => FractionalIdeal.count L p (X : FractionalIdeal (𝓞 L)⁰ L)) h
  simp only [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow] at h1
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hl) h1

private theorem root_exists {L : Type} [Field L] [NumberField L] {l : ℕ} (y : Lˣ)
    (h : ∀ p : HeightOneSpectrum (𝓞 L), (l : ℤ) ∣ ordP p y) :
    ∃ I : (FractionalIdeal (𝓞 L)⁰ L)ˣ, I ^ l = toPrincipalIdeal (𝓞 L) L y := by
  have hf : ∀ᶠ p : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ordP p y / l = 0 := by
    filter_upwards [FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L))] with p hp
    rw [ord_eq_count, hp, Int.zero_ediv]
  have h0 : (∏ᶠ p : HeightOneSpectrum (𝓞 L), (p.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ (ordP p y / l)) ≠ 0 := by
    refine finprod_induction (fun X => X ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)
  refine ⟨Units.mk0 _ h0, Units.ext (fi_ext (Units.ne_zero _) (Units.ne_zero _) fun p => ?_)⟩
  rw [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_mk0, FractionalIdeal.count_finprod L p _ hf,
    coe_toPrincipalIdeal, ← ord_eq_count, Int.mul_ediv_cancel' (h p)]

private theorem primes_card (L : Type) [Field L] [NumberField L] {l : ℕ} (hl : l.Prime) :
    Finite {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} ∧
      Nat.card {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} ≤ Module.finrank ℚ L := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hp.ne_zero
  haveI hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal hne
  let f : {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} →
      IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 L) := fun p =>
    ⟨p.1.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 L)).mpr ⟨p.1.isPrime, ⟨by
      haveI := p.1.isPrime
      refine hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact p.2⟩⟩⟩
  have hf : Function.Injective f := fun p q h =>
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 L) ℚ L hne

private theorem zpow_eq_val {Q : Type} [Group Q] {l : ℕ} [NeZero l] (x : Q) (hx : x ^ l = 1) (m : ℤ) :
    x ^ m = x ^ (m : ZMod l).val := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' m hx]

private theorem units_card (L : Type) [Field L] [NumberField L] {l : ℕ} (hl : l.Prime) {Q : Type} [CommGroup Q]
    (hQ : ∀ x : Q, x ^ l = 1) (f : (𝓞 L)ˣ →* Q) :
    Finite f.range ∧ Nat.card f.range ≤ l ^ Module.finrank ℚ L := by
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Units.torsion L)
  let g : ZMod l × (Fin (Units.rank L) → ZMod l) → f.range := fun e =>
    ⟨f ((ζ : (𝓞 L)ˣ) ^ e.1.val * ∏ i, Units.fundSystem L i ^ (e.2 i).val), _, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨_, u, rfl⟩
    obtain ⟨⟨t, e⟩, rfl, -⟩ := Units.exist_unique_eq_mul_prod L u
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hζ t)
    refine ⟨((k : ZMod l), fun i => (e i : ZMod l)), Subtype.ext ?_⟩
    simp only [g, map_mul, map_prod, map_pow, map_zpow, SubgroupClass.coe_zpow]
    rw [← zpow_eq_val _ (hQ _)]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (zpow_eq_val _ (hQ _) _).symm
  refine ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans ?_⟩
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_succ']
  refine Nat.pow_le_pow_right hl.pos ?_
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
  unfold Units.rank
  omega

private theorem exp_card {l : ℕ} (hl : l.Prime) {C : Type} [Group C] [Finite C] (R : Subgroup C)
    (hR : ∀ x ∈ R, x ^ l = 1) : Nat.card R ≤ l ^ Nat.log 2 (Nat.card C) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : IsPGroup l R := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hR x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 : Nat.card R ≤ Nat.card C := Nat.card_le_card_of_injective _ R.subtype_injective
  rw [hk] at h1 ⊢
  refine Nat.pow_le_pow_right hl.pos (Nat.le_log_of_pow_le one_lt_two ?_)
  exact (Nat.pow_le_pow_left hl.two_le k).trans h1

private theorem index_le {G T : Type} [Group G] [Group T] [Finite T] (f : G →* T) (K : Subgroup G)
    (h : f.ker ≤ K) : K.index ≠ 0 ∧ K.index ≤ Nat.card f.range := by
  have hd := Subgroup.index_dvd_of_le h
  rw [Subgroup.index_ker] at hd
  have hp : 0 < Nat.card f.range := Nat.card_pos
  exact ⟨ne_zero_of_dvd_ne_zero hp.ne' hd, Nat.le_of_dvd hp hd⟩

theorem UpperTheory.V.ZK.Ct.selLCard :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ), l.Prime → Finite (SelL l L) ∧ Nat.card (SelL l L) ≤ l ^ (2 * Module.finrank ℚ L + Nat.log 2 (classNumber L)) := by
  intro L _ _ l hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  let P : Subgroup Lˣ := (powMonoidHom l : Lˣ →* Lˣ).range
  let q : Lˣ →* Lˣ ⧸ P := QuotientGroup.mk' P
  let ι : (𝓞 L)ˣ →* Lˣ := Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L)
  let π := toPrincipalIdeal (𝓞 L) L
  let U : Subgroup Lˣ := (q.comp ι).range.comap q
  let H0 : Subgroup Lˣ :=
    (powMonoidHom l : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ).range.comap π
  let H : Subgroup Lˣ :=
    { carrier := {y | ∀ p : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∉ p.asIdeal → (l : ℤ) ∣ ordP p y}
      one_mem' := fun p _ => by rw [ord_one]; exact dvd_zero _
      mul_mem' := fun ha hb p hp => by rw [ord_mul]; exact dvd_add (ha p hp) (hb p hp)
      inv_mem' := fun ha p hp => by rw [ord_inv]; exact (ha p hp).neg_right }
  have hqk : q.ker = P := QuotientGroup.ker_mk' P
  have hql : ∀ z : Lˣ, q (z ^ l) = 1 := fun z => (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  have hπι : ∀ u, π (ι u) = 1 := fun u => by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]
    change algebraMap (𝓞 L) L _ * algebraMap (𝓞 L) L _ = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hPU : q.ker ≤ U := fun y hy => by
    change q y ∈ (q.comp ι).range
    rw [MonoidHom.mem_ker.mp hy]; exact one_mem _
  have hU0 : U ≤ H0 := by
    rintro y ⟨u, hu⟩
    obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hu
    refine ⟨π z, ?_⟩
    rw [powMonoidHom_apply] at hz ⊢
    rw [← map_pow, hz, map_mul, map_inv, hπι, inv_one, one_mul]
  have h0H : H0 ≤ H := by
    rintro y ⟨I, hI⟩ p -
    rw [ord_eq_count, ← coe_toPrincipalIdeal, ← hI, powMonoidHom_apply, Units.val_pow_eq_pow_val,
      FractionalIdeal.count_pow]
    exact Dvd.intro _ rfl

  have hQ : ∀ x : Lˣ ⧸ P, x ^ l = 1 := fun x => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective P x
    rw [← map_pow]; exact hql z
  obtain ⟨hf1, hc1⟩ := units_card L hl hQ (q.comp ι)
  have e1 : q.ker.relIndex U = Nat.card (q.comp ι).range := by
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective P)]
  have n1 : q.ker.relIndex U ≠ 0 := by rw [e1]; exact Nat.card_pos.ne'

  have hr : ∀ y : H0, ∃ I : (FractionalIdeal (𝓞 L)⁰ L)ˣ, I ^ l = π y := fun y => y.2
  choose r hr using hr
  let ψ : H0 →* ClassGroup (𝓞 L) := MonoidHom.mk' (fun y => ClassGroup.mk L (r y)) fun x y => by
    rw [← map_mul]
    congr 1
    apply root_unique hl.ne_zero
    rw [mul_pow, hr, hr, hr, Subgroup.coe_mul, map_mul]
  have hψ : ψ.ker ≤ U.subgroupOf H0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (FractionalIdeal.isPrincipal_iff _).mp (ClassGroup.mk_eq_one_iff.mp hy)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (r y).ne_zero (by rw [hz, FractionalIdeal.spanSingleton_zero])
    have h1 := congrArg Units.val (hr y)
    rw [Units.val_pow_eq_pow_val, hz, FractionalIdeal.spanSingleton_pow, coe_toPrincipalIdeal,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 : (y : Lˣ) = ι u * Units.mk0 z hz0 ^ l := by
      apply Units.ext
      rw [← hu, Units.smul_def, Algebra.smul_def, Units.val_mul, Units.val_pow_eq_pow_val]
      rfl
    refine ⟨u, ?_⟩
    change q (ι u) = q y
    rw [h2, map_mul, hql, mul_one]
  obtain ⟨n2, c2⟩ := index_le ψ _ hψ
  have c2' : Nat.card ψ.range ≤ l ^ Nat.log 2 (classNumber L) := by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    refine exp_card hl _ ?_
    rintro _ ⟨y, rfl⟩
    change ClassGroup.mk L (r y) ^ l = 1
    rw [← map_pow, hr, ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
    exact ⟨_, coe_toPrincipalIdeal _⟩

  obtain ⟨hf3, hc3⟩ := primes_card L hl
  let φ : H →* Multiplicative ({p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} → ZMod l) :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd fun p => (ordP p.1 (y : Lˣ) : ZMod l)) fun x y => by
      rw [← ofAdd_add]
      congr 1
      funext p
      rw [Subgroup.coe_mul, ord_mul, Int.cast_add, Pi.add_apply]
  have hφ : φ.ker ≤ H0.subgroupOf H := by
    intro y hy
    refine root_exists (y : Lˣ) fun p => ?_
    by_cases hp : (l : 𝓞 L) ∈ p.asIdeal
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (congrFun (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hy)) ⟨p, hp⟩)
    · exact y.2 p hp
  obtain ⟨n3, c3⟩ := index_le φ _ hφ
  have c3' : Nat.card φ.range ≤ l ^ Module.finrank ℚ L := by
    refine (Nat.card_le_card_of_injective _ φ.range.subtype_injective).trans ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod]
    exact Nat.pow_le_pow_right hl.pos hc3

  have hS : SelL l L = (H.map q : Set (Lˣ ⧸ P)) := by
    ext x
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩
  have hcard : Nat.card (SelL l L) = q.ker.relIndex U * U.relIndex H0 * H0.relIndex H := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hPU hU0,
      Subgroup.relIndex_mul_relIndex _ _ _ (hPU.trans hU0) h0H, Subgroup.relIndex_ker, hS]
    rfl
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hcard]
    exact mul_ne_zero (mul_ne_zero n1 n2) n3
  · rw [hcard, show 2 * Module.finrank ℚ L + Nat.log 2 (classNumber L) =
      Module.finrank ℚ L + Nat.log 2 (classNumber L) + Module.finrank ℚ L by ring, pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (e1.trans_le hc1) (c2.trans c2')) (c3.trans c3')
