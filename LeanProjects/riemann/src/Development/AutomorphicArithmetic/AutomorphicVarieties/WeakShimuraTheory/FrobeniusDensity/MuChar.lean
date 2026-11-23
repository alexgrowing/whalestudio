import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RayChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.FrobDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.QuadFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem unit_pow (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (h : Module.finrank ℚ K = 2) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : (𝓞 K)ˣ, u ^ m = 1 := by
  have hr : Units.rank K = 0 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, h] at h1
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  refine ⟨Nat.card (Units.torsion K), Nat.card_pos, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, h1, -⟩ := Units.exist_unique_eq_mul_prod K u
  haveI : IsEmpty (Fin (Units.rank K)) := by rw [hr]; infer_instance
  rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h1
  rw [h1, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]

private theorem class_pow (K : Type) [Field K] [NumberField K] :
    ∃ h : ℕ, 0 < h ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∃ a : 𝓞 K, I ^ h = Ideal.span {a} := by
  refine ⟨Nat.card (ClassGroup (𝓞 K)), Nat.card_pos, fun I hI => ?_⟩
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  have h1 : ClassGroup.mk0 ((⟨I, hm⟩ : nonZeroDivisors (Ideal (𝓞 K))) ^ Nat.card (ClassGroup (𝓞 K))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact ((ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hm _)).1 h1).principal

private theorem exists_iota {R : Type} [CommRing R] {l : ℕ} [Fact l.Prime] (w : Ideal R)
    (h : ∀ n : ℕ, ∃ φ : R →+* ZMod (l ^ n), RingHom.ker φ = w ^ n) :
    ∃ ι : R →+* ℤ_[l], ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n := by
  choose φ hφ using h
  have hc : ∀ (k1 k2) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (φ k2) = φ k1 := by
    intro k1 k2 hk
    ext x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (φ k2 x)
    have h1 : x - z ∈ RingHom.ker (φ k1) := by
      rw [hφ]
      refine Ideal.pow_le_pow_right hk ?_
      rw [← hφ, RingHom.mem_ker, map_sub, map_intCast, hz, sub_self]
    rw [RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero] at h1
    rw [RingHom.comp_apply, ← hz, map_intCast, h1]
  refine ⟨PadicInt.lift hc, fun n x => ?_⟩
  rw [← RingHom.comp_apply, PadicInt.lift_spec, ← hφ, RingHom.mem_ker]

private theorem cont_of_open {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C]
    [TopologicalSpace C] [IsTopologicalGroup C] (κ : Γ →* C) (h : IsOpen (κ.ker : Set Γ)) : Continuous κ := by
  refine continuous_of_continuousAt_one κ ?_
  refine (continuousAt_const (y := (1 : C))).congr ?_
  filter_upwards [h.mem_nhds (one_mem κ.ker)] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm

private theorem exists_limit {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {l : ℕ} [hl : Fact l.Prime]
    (D : Set Γ) (hD : Dense D) (κ : ∀ k : ℕ, Γ →* (ZMod (l ^ k))ˣ) (ho : ∀ k, IsOpen ((κ k).ker : Set Γ))
    (hx : ∀ s ∈ D, ∃ u : ℤ_[l], ∀ k, (κ k s : ZMod (l ^ k)) = PadicInt.toZModPow k u) :
    ∃ μ : Γ →* ℤ_[l]ˣ, Continuous μ ∧ ∀ k s, PadicInt.toZModPow k (μ s : ℤ_[l]) = κ k s := by
  let f : ∀ k : ℕ, MonoidAlgebra ℤ Γ →+* ZMod (l ^ k) := fun k =>
    (MonoidAlgebra.lift ℤ (ZMod (l ^ k)) Γ ((Units.coeHom _).comp (κ k))).toRingHom
  have hf : ∀ k s, f k (MonoidAlgebra.of ℤ Γ s) = κ k s := fun k s => MonoidAlgebra.lift_of _ _
  have hc : ∀ (k1 k2) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2) = f k1 := by
    intro k1 k2 hk
    refine MonoidAlgebra.ringHom_ext' (RingHom.ext_int _ _) (MonoidHom.ext fun s => ?_)
    show ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1)) (f k2 (MonoidAlgebra.of ℤ Γ s)) = f k1 (MonoidAlgebra.of ℤ Γ s)
    rw [hf, hf]
    have c1 : Continuous fun s => (κ k1 s : ZMod (l ^ k1)) := Units.continuous_val.comp (cont_of_open _ (ho k1))
    have c2 : Continuous fun s => ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1)) (κ k2 s : ZMod (l ^ k2)) :=
      continuous_of_discreteTopology.comp (Units.continuous_val.comp (cont_of_open _ (ho k2)))
    refine congrFun (Continuous.ext_on hD c2 c1 fun t ht => ?_) s
    obtain ⟨u, hu⟩ := hx t ht
    show ZMod.castHom _ _ _ = _
    rw [hu, hu, ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ hk]
  let ν : Γ →* ℤ_[l] := (PadicInt.lift hc).toMonoidHom.comp (MonoidAlgebra.of ℤ Γ)
  have hν : ∀ k s, PadicInt.toZModPow k (ν s) = κ k s := fun k s => by
    rw [← hf, ← PadicInt.lift_spec hc k]; rfl
  have cν : Continuous ν := by
    refine continuous_iff_continuousAt.2 fun s => Metric.continuousAt_iff'.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have c1 : Continuous fun s => (κ k s : ZMod (l ^ k)) := Units.continuous_val.comp (cont_of_open _ (ho k))
    filter_upwards [((isOpen_discrete {(κ k s : ZMod (l ^ k))}).preimage c1).mem_nhds rfl] with t ht
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hν, hν,
      sub_eq_zero]
    exact ht
  refine ⟨ν.toHomUnits, Units.continuous_iff.2 ⟨cν, ?_⟩, hν⟩
  have : (fun s => ((ν.toHomUnits s)⁻¹ : ℤ_[l]ˣ).val) = fun s => ν s⁻¹ := by
    funext s; rw [← map_inv]; rfl
  rw [this]
  exact cν.comp continuous_inv

private theorem iota_unit {R : Type} [CommRing R] {l : ℕ} [hl : Fact l.Prime] {w : Ideal R} {ι : R →+* ℤ_[l]}
    (h : ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n) {a : R} (ha : IsCoprime (Ideal.span {a}) w) :
    IsUnit (ι a) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : ι y ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker, h, pow_one]
    exact hy
  have h2 : IsUnit (1 - ι y) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h1
  rw [← map_one ι, ← map_sub, ← hxy, add_sub_cancel_right, map_mul] at h2
  exact isUnit_of_mul_isUnit_right h2

private theorem unit_fermat {l : ℕ} [hl : Fact l.Prime] {x : ℤ_[l]} (hx : IsUnit x) (m : ℕ) :
    ‖x ^ (m * (l - 1)) - 1‖ < 1 := by
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one (hx.map _).ne_zero, one_pow, map_one, sub_self]

private theorem exists_F (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [hl : Fact l.Prime] {w : Ideal (𝓞 K)} {ι : 𝓞 K →+* ℤ_[l]}
    (hι : ∀ n x, PadicInt.toZModPow n (ι x) = 0 ↔ x ∈ w ^ n) :
    ∃ (F : Ideal (𝓞 K) → ℤ_[l]ˣ) (n : ℕ), 0 < n ∧
      (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I w → IsCoprime J w → F (I * J) = F I * F J) ∧
      (∀ a, IsCoprime (Ideal.span {a}) w → (F (Ideal.span {a}) : ℤ_[l]) = ι a ^ n) ∧
      ∀ I, I ≠ ⊥ → IsCoprime I w → ‖(F I : ℤ_[l]) - 1‖ < 1 := by
  classical
  obtain ⟨m, hm, hu⟩ := unit_pow K hK
  obtain ⟨h, hh, hc⟩ := class_pow K
  let P : Ideal (𝓞 K) → ℤ_[l]ˣ → Prop := fun I u => ∃ a, I ^ h = Ideal.span {a} ∧ (u : ℤ_[l]) = ι a ^ (m * (l - 1))
  have uniq : ∀ I u v, P I u → P I v → u = v := by
    rintro I u v ⟨a, ha, hu'⟩ ⟨b, hb, hv⟩
    obtain ⟨e, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 (ha.symm.trans hb)
    apply Units.ext
    rw [hu', hv, map_mul, mul_pow, ← map_pow ι (e : 𝓞 K), pow_mul (e : 𝓞 K), ← Units.val_pow_eq_pow_val, hu]
    simp
  let F : Ideal (𝓞 K) → ℤ_[l]ˣ := fun I => if hI : ∃ u, P I u then hI.choose else 1
  have hF : ∀ I u, P I u → F I = u := fun I u hI => by
    have h1 : ∃ u, P I u := ⟨u, hI⟩
    simp only [F, dif_pos h1]
    exact uniq I _ _ h1.choose_spec hI
  have ex : ∀ I, I ≠ ⊥ → IsCoprime I w → ∃ a, IsUnit (ι a) ∧ I ^ h = Ideal.span {a} ∧
      (F I : ℤ_[l]) = ι a ^ (m * (l - 1)) := fun I hI hw => by
    obtain ⟨a, ha⟩ := hc I hI
    have h1 : IsUnit (ι a) := iota_unit hι (ha ▸ hw.pow_left)
    refine ⟨a, h1, ha, ?_⟩
    rw [hF I (h1.unit ^ (m * (l - 1))) ⟨a, ha, by simp⟩]
    simp
  refine ⟨F, h * (m * (l - 1)), Nat.mul_pos hh (Nat.mul_pos hm (Nat.sub_pos_of_lt hl.out.one_lt)), ?_, ?_, ?_⟩
  · intro I J hI hJ hI' hJ'
    obtain ⟨a, -, ha, ha'⟩ := ex I hI hI'
    obtain ⟨b, -, hb, hb'⟩ := ex J hJ hJ'
    refine hF _ _ ⟨a * b, ?_, ?_⟩
    · rw [mul_pow, ha, hb, Ideal.span_singleton_mul_span_singleton]
    · rw [Units.val_mul, ha', hb', map_mul, mul_pow]
  · intro a ha
    have h1 : IsUnit (ι a) := iota_unit hι ha
    rw [hF _ (h1.unit ^ (h * (m * (l - 1)))) ⟨a ^ h, Ideal.span_singleton_pow _ _, by simp [pow_mul]⟩]
    simp
  · intro I hI hw
    obtain ⟨a, h1, -, ha⟩ := ex I hI hw
    rw [ha]
    exact unit_fermat h1 m

private theorem exists_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : IntermediateField ℚ Ω)
    [NumberField K] (hK : Module.finrank ℚ K = 2) (c : G ℚ Ω) :
    ∃ j : G K Ω → G K Ω, Continuous j ∧ (∀ s, resQ K (j s) = c * resQ K s * c⁻¹) ∧ Function.Injective (resQ K) := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have he := (galEmbTop ℚ K Ω).1
  have h1 : ∀ s, ∃ t, galEmb ℚ K Ω t = c * galEmb ℚ K Ω s * c⁻¹ := fun s => by
    have := (galOf_normal ℚ K Ω).conj_mem _ (galEmb_mem ℚ K Ω s) c
    rwa [← range_galEmb] at this
  choose j hj using h1
  refine ⟨j, he.continuous_iff.2 ?_, hj, he.injective⟩
  have : galEmb ℚ K Ω ∘ j = fun s => c * galEmb ℚ K Ω s * c⁻¹ := funext hj
  rw [this]
  exact (continuous_const.mul he.continuous).mul continuous_const

theorem UpperTheory.V.Ws.Tw.muChar :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ (μ : G K Ω →* ℤ_[l]ˣ) (n : ℕ), 0 < n ∧ Continuous μ ∧ (∀ s, ‖(μ s : ℤ_[l]) - 1‖ < 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → μ s * μ s' = cycZ K Ω l s ^ n) ∧ ∀ B : ValuationSubring Ω, (∃ x ∈ K, ¬ (x ∈ B ↔ x ∈ A)) → Ine (F := K) B ≤ μ.ker := by
  intro Ω _ _ _ l hl hl2 K _ _ hK A hA hDec
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨τ, -, hN, hconj, hsplit, -⟩ := Tw.quadFacts Ω l hl2 K hK
  obtain ⟨w, hw, -, -, hφ⟩ := hsplit l A hl.out hA hDec
  obtain ⟨ι, hι⟩ := exists_iota w.asIdeal hφ
  obtain ⟨F, n, hn, hmul, hpr, hone⟩ := exists_F K hK hι
  have hlw : (l : 𝓞 K) ∈ w.asIdeal := ((places K Ω l A).2.2.1 w hw).1 hA
  have hray : ∀ k : ℕ, ∃ κ : G K Ω →* (ZMod (l ^ k))ˣ, IsOpen (κ.ker : Set (G K Ω)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → ∀ B : ValuationSubring Ω, IsPlaceOver B v → Ine (F := K) B ≤ κ.ker ∧
        ∀ σ : G K Ω, IsFrob B (normV v) σ → (κ σ : ZMod (l ^ k)) = PadicInt.toZModPow k (F v.asIdeal : ℤ_[l]) := by
    intro k
    obtain ⟨κ, h1, h2⟩ := Tw.rayChar K Ω (w.asIdeal ^ (k + 1)) (pow_ne_zero _ w.ne_bot) (ZMod (l ^ k))ˣ
      (fun I => Units.map (PadicInt.toZModPow k).toMonoidHom (F I))
      (fun I J hI hJ hI' hJ' => by
        rw [hmul I J hI hJ ((IsCoprime.pow_right_iff k.succ_pos).1 hI') ((IsCoprime.pow_right_iff k.succ_pos).1 hJ'),
          map_mul])
      (fun a _ ha => by
        have hc : IsCoprime (Ideal.span {a}) w.asIdeal :=
          Ideal.isCoprime_iff_exists.2 ⟨a, Ideal.mem_span_singleton_self a, -(a - 1),
            neg_mem (Ideal.pow_le_self k.succ_ne_zero ha), by ring⟩
        have h3 := (hι k _).2 (Ideal.pow_le_pow_right k.le_succ ha)
        rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h3
        apply Units.ext
        show PadicInt.toZModPow k (F _ : ℤ_[l]) = 1
        rw [hpr a hc, map_pow, h3, one_pow])
    refine ⟨κ, h1, fun v hv B hB => ?_⟩
    obtain ⟨h3, h4⟩ := h2 v (fun hd => hv (HeightOneSpectrum.ext
      ((prime_dvd_prime_iff_eq v.prime w.prime).1 (v.prime.dvd_of_dvd_pow hd)))) B hB
    exact ⟨h3, fun σ hσ => by rw [h4 σ hσ]; rfl⟩
  choose κ hκo hκ using hray
  have hl0 : Ideal.span {(l : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero
  have hD := Tw.frobDense K Ω _ hl0
  simp only [Ideal.dvd_span_singleton] at hD
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ v.asIdeal → v ≠ w := fun v hv h => hv (h ▸ hlw)
  have hcop : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → IsCoprime v.asIdeal w.asIdeal := fun v hv =>
    Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal fun h => hv (HeightOneSpectrum.ext h))
  obtain ⟨μ, hμc, hμ⟩ := exists_limit _ hD κ hκo (by
    rintro s ⟨v, B, hv, hB, hs⟩
    exact ⟨_, fun k => (hκ k v (hne v hv) B hB).2 s hs⟩)
  have hfr : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w → ∀ B, IsPlaceOver B v → ∀ σ : G K Ω, IsFrob B (normV v) σ →
      μ σ = F v.asIdeal := fun v hv B hB σ hσ =>
    Units.ext (PadicInt.ext_of_toZModPow.1 fun k => by rw [hμ, (hκ k v hv B hB).2 σ hσ])
  refine ⟨μ, n, hn, hμc, fun s => ?_, fun c hc s s' hs => ?_, fun B ⟨x, hxK, hx⟩ => ?_⟩
  · have hcl : IsClosed {s : G K Ω | (μ s : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) 1} :=
      (IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp hμc)
    have h1 := hD.induction (P := fun s : G K Ω => (μ s : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) 1) ?_ hcl s
    · rwa [mem_ball_iff_norm] at h1
    · rintro t ⟨v, B, hv, hB, ht⟩
      rw [mem_ball_iff_norm, hfr v (hne v hv) B hB t ht]
      exact hone _ v.ne_bot (hcop v (hne v hv))
  · obtain ⟨j, hjc, hj, hinj⟩ := exists_conj K hK c
    obtain rfl : s' = j s := hinj (hs.trans (hj s).symm)
    refine congrFun (Continuous.ext_on hD (hμc.mul (hμc.comp hjc)) ((continuous_cycZ K Ω l).pow n) ?_) s
    rintro t ⟨v, B, hv, hB, ht⟩
    obtain ⟨v', B', e, hB', ht'⟩ := hconj c hc t (j t) (hj t) v B hB ht
    have hv' : (l : 𝓞 K) ∉ v'.asIdeal := by
      rw [e, Ideal.mem_map_iff_of_surjective τ τ.surjective]
      rintro ⟨y, hy, hy'⟩
      rw [← map_natCast τ] at hy'
      exact hv (τ.injective hy' ▸ hy)
    have c1 := hcop v (hne v hv)
    have c2 := hcop v' (hne v' hv')
    have c3 := c1.mul_left c2
    show μ t * μ (j t) = cycZ K Ω l t ^ n
    rw [hfr v (hne v hv) B hB t ht, hfr v' (hne v' hv') B' hB' _ ht', ← hmul _ _ v.ne_bot v'.ne_bot c1 c2]
    rw [e, hN] at c3
    apply Units.ext
    rw [e, hN, hpr _ c3, Units.val_pow_eq_pow_val, cycZ_of_isFrob hv hB ht, map_natCast]
    rfl
  · by_cases hB : B = ⊤
    · rw [((places K Ω l B).2.1 hB).1]
      exact bot_le
    obtain ⟨v, hv⟩ := (places K Ω l B).1 hB
    have hvw : v ≠ w := by
      rintro rfl
      obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := K) hw hv
      apply hx
      have h1 : g • x = x := g.commutes ⟨x, hxK⟩
      rw [← hg]
      conv_lhs => rw [← h1]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    intro s hs
    rw [MonoidHom.mem_ker]
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    rw [hμ, MonoidHom.mem_ker.1 ((hκ k v hvw B hv).1 hs)]
    simp
