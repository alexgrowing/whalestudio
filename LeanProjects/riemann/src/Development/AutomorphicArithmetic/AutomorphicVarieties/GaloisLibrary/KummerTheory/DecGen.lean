import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem frob_pow_fin (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (τ : L →ₐ[k] L) (S : Finset L) : ∃ i : ℕ, ∀ x ∈ S, τ x = x ^ Nat.card k ^ i := by
  classical
  haveI := Fintype.ofFinite k
  let E := IntermediateField.adjoin k (S : Set L)
  haveI : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : Finite E := Module.finite_of_finite k
  haveI : Normal k E := inferInstance
  let τE : E →ₐ[k] E := τ.restrictNormal E
  have hbij : Function.Bijective τE := Finite.injective_iff_bijective.1 τE.toRingHom.injective
  let e : E ≃ₐ[k] E := AlgEquiv.ofBijective τE hbij
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2 e
  have hn' : FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ (n : ℕ) = e := hn
  refine ⟨n, fun x hx => ?_⟩
  have hxE : x ∈ E := IntermediateField.subset_adjoin k _ hx
  have h1 := τ.restrictNormal_commutes E ⟨x, hxE⟩
  have h3 : e ⟨x, hxE⟩ = ⟨x, hxE⟩ ^ Fintype.card k ^ (n : ℕ) := by
    rw [← hn', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [Nat.card_eq_fintype_card]
  calc τ x = τ (algebraMap E L ⟨x, hxE⟩) := rfl
    _ = algebraMap E L (τE ⟨x, hxE⟩) := h1.symm
    _ = algebraMap E L (e ⟨x, hxE⟩) := rfl
    _ = x ^ Fintype.card k ^ (n : ℕ) := by
      rw [h3, map_pow]
      rfl

private theorem alg_residue {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (k : Type) [Field k]
    [Algebra k (IsLocalRing.ResidueField A)] (x : A) (hx : IsAlgebraic ℤ (x : Ω)) :
    IsAlgebraic k (IsLocalRing.residue A x) := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have hq : p.primPart.IsPrimitive := p.isPrimitive_primPart
  have hqx : Polynomial.aeval x p.primPart = 0 := by
    have h1 : Polynomial.aeval (x : Ω) p = (p.content : Ω) * Polynomial.aeval (x : Ω) p.primPart := by
      conv_lhs => rw [p.eq_C_content_mul_primPart]
      simp
    have hc : (p.content : Ω) ≠ 0 := by
      exact_mod_cast (Polynomial.content_eq_zero_iff.not.2 hp0)
    rw [hpx] at h1
    have h2 : Polynomial.aeval (x : Ω) p.primPart = 0 := (mul_eq_zero.1 h1.symm).resolve_left hc
    have h3 : ((Polynomial.aeval x p.primPart : A) : Ω) = Polynomial.aeval (x : Ω) p.primPart :=
      (Polynomial.aeval_algebraMap_apply Ω x p.primPart).symm
    apply Subtype.ext
    rw [h3, h2]
    rfl
  refine ⟨p.primPart.map (algebraMap ℤ k), ?_, ?_⟩
  · intro h
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hr | hr
    · have hdvd : Polynomial.C ((ringChar k : ℕ) : ℤ) ∣ p.primPart := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (fun P => Polynomial.coeff P i) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
        exact (CharP.intCast_eq_zero_iff k (ringChar k) _).1 this
      have hu := hq _ hdvd
      rw [Int.isUnit_iff] at hu
      have := hr.two_le
      omega
    · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).1 hr
      have : p.primPart = 0 := by
        apply Polynomial.map_injective (algebraMap ℤ k) (RingHom.injective_int (algebraMap ℤ k))
        rw [h, Polynomial.map_zero]
      exact hq.ne_zero this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap k (IsLocalRing.ResidueField A)).comp (algebraMap ℤ k) =
        algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
    rw [e, ← Polynomial.aeval_def]
    have := Polynomial.aeval_algebraMap_apply (IsLocalRing.ResidueField A) x p.primPart
    rw [IsLocalRing.ResidueField.algebraMap_eq] at this
    rw [this, hqx, map_zero]

private theorem frob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (hφ : IsFrob A q φ) (n : ℕ) :
    IsFrob A (q ^ n) (φ ^ n) := by
  have hD : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero =>
    refine ⟨by rw [pow_zero]; exact one_mem _, fun x _ => ?_⟩
    simp
  | succ n ih =>
    refine ⟨pow_mem hD (n + 1), fun x hx => ?_⟩
    have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    have hyA : (φ ^ n) x ∈ A := (apply_mem_iff_of_mem_Dec (pow_mem hD n) x).2 hxA
    have hxA' : x ^ q ^ n ∈ A := pow_mem hxA _
    have e1 : A.valuation (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) < 1 :=
      hφ.2 _ ((A.valuation_le_one_iff _).2 hyA)
    have e2 : A.valuation ((φ ^ n) x - x ^ q ^ n) < 1 := ih.2 x hx
    have e3 : A.valuation (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) < 1 := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨(φ ^ n) x, hyA⟩ : A) ⟨x ^ q ^ n, hxA'⟩ q
      have h4 : ((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q = ((φ ^ n) x - x ^ q ^ n) * c := by
        have := congrArg (fun z : A => (z : Ω)) hc
        push_cast at this
        exact this
      rw [h4, map_mul]
      have hc1 : A.valuation (c : Ω) ≤ 1 := A.valuation_le_one c
      calc _ ≤ A.valuation ((φ ^ n) x - x ^ q ^ n) * 1 := by gcongr
        _ < 1 := by
          rw [mul_one]
          exact e2
    have h5 : (φ ^ (n + 1)) x - x ^ q ^ (n + 1) =
        (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) + (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) := by
      rw [pow_succ' φ n, AlgEquiv.mul_apply, pow_succ q n, pow_mul]
      ring
    rw [h5]
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt e1 e3)

private theorem dec_pow_fin {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) (S : Finset A) :
    ∃ i : ℕ, ∀ x ∈ S, A.valuation (g x - (x : Ω) ^ normV v ^ i) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hint : ∀ a : 𝓞 K, ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) a ∈ A := fun a =>
    mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω))
  let f0 : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let f1 : 𝓞 K →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp f0
  have hker : ∀ a ∈ v.asIdeal, f1 a = 0 := by
    intro a ha
    show IsLocalRing.residue A (f0 a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (hA a).2 ha
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) :=
    (Ideal.Quotient.lift v.asIdeal f1 hker).toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  haveI : Algebra.IsAlgebraic (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact alg_residue A _ x ((IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic (x : Ω)))⟩
  let gD : ValuationSubring.decompositionSubgroup K A := ⟨g, hg⟩
  have hfix : ∀ a : 𝓞 K, gD • f0 a = f0 a := by
    intro a
    apply Subtype.ext
    show g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
    exact g.commutes _
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 K ⧸ v.asIdeal] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) gD with
      commutes' := by
        intro c
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        show gD • (Ideal.Quotient.lift v.asIdeal f1 hker (Ideal.Quotient.mk _ a)) = _
        rw [Ideal.Quotient.lift_mk]
        show gD • IsLocalRing.residue A (f0 a) = IsLocalRing.residue A (f0 a)
        rw [← IsLocalRing.ResidueField.residue_smul (ValuationSubring.decompositionSubgroup K A) gD (f0 a), hfix] }
  obtain ⟨i, hi⟩ := frob_pow_fin (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) τ
    (S.image (IsLocalRing.residue A))
  refine ⟨i, fun x hx => ?_⟩
  have h1 : gD • IsLocalRing.residue A x = IsLocalRing.residue A x ^ normV v ^ i :=
    hi _ (Finset.mem_image_of_mem _ hx)
  have h2 : IsLocalRing.residue A (gD • x - x ^ normV v ^ i) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, map_pow, h1, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

private theorem closed_ev {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω)
    (P : Ω → Prop) : IsClosed {h : G K Ω | P (h x)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨(fun k => h * k) '' (((IntermediateField.adjoin K {x}).fixingSubgroup : Subgroup (G K Ω)) : Set (G K Ω)),
    ?_, ?_, ⟨1, one_mem _, mul_one h⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    have hkx : k x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk x (IntermediateField.mem_adjoin_simple_self K x)
    show ¬ P ((h * k) x)
    rw [AlgEquiv.mul_apply, hkx]
    exact hh
  · exact isOpenMap_mul_left h _ (IntermediateField.fixingSubgroup_isOpen _)

theorem UpperTheory.V.Kum.decGen :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω) (H : Subgroup (G K Ω)),
    IsPlaceOver A v → IsFrob (F := K) A (normV v) σ → IsOpen (H : Set (G K Ω)) → Ine (F := K) A ≤ H → σ ∈ H → Dec (F := K) A ≤ H := by
  classical
  intro K Ω _ _ _ _ _ A v σ H hA hσ hHo hI hσH g hg
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hHc : IsClosed (H : Set (G K Ω)) := Subgroup.isClosed_of_isOpen H hHo
  have hσD : σ ∈ Dec (F := K) A := hσ.1
  have hDc : IsClosed (Dec (F := K) A : Set (G K Ω)) := by
    have e : (Dec (F := K) A : Set (G K Ω)) = ⋂ x : Ω, {h : G K Ω | (h x ∈ A ↔ x ∈ A)} := by
      ext h
      simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
      constructor
      · intro hh x
        exact apply_mem_iff_of_mem_Dec hh x
      · intro hh
        rw [mem_Dec]
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
        have h1 := hh (h⁻¹ y)
        rw [AlgEquiv.aut_inv] at h1 ⊢
        rw [AlgEquiv.apply_symm_apply] at h1
        exact h1.symm
    rw [e]
    exact isClosed_iInter fun x => closed_ev x (fun y => (y ∈ A ↔ x ∈ A))
  let Cl : Set (G K Ω) := closure (Set.range fun i : ℕ => σ ^ i)
  have hClH : Cl ⊆ H := closure_minimal (by
    rintro _ ⟨i, rfl⟩
    exact H.pow_mem hσH i) hHc
  have hClD : Cl ⊆ Dec (F := K) A := closure_minimal (by
    rintro _ ⟨i, rfl⟩
    exact (Dec (F := K) A).pow_mem hσD i) hDc
  let C : Finset A → Set (G K Ω) := fun S => Cl ∩ {τ | ∀ x ∈ S, A.valuation (g x - τ x) < 1}
  have hCcl : ∀ S, IsClosed (C S) := by
    intro S
    apply isClosed_closure.inter
    have e : {τ : G K Ω | ∀ x ∈ S, A.valuation (g x - τ x) < 1} =
        ⋂ x ∈ S, {τ : G K Ω | A.valuation (g x - τ x) < 1} := by
      ext τ
      simp
    rw [e]
    exact isClosed_biInter fun x _ => closed_ev (x : Ω) (fun y => A.valuation (g x - y) < 1)
  have hCne : ∀ S, (C S).Nonempty := by
    intro S
    obtain ⟨i, hi⟩ := dec_pow_fin hA hg S
    refine ⟨σ ^ i, subset_closure ⟨i, rfl⟩, fun x hx => ?_⟩
    have h1 := hi x hx
    have h2 := (frob_pow hσ i).2 x (A.valuation_le_one x)
    have e : g x - (σ ^ i) x = (g x - (x : Ω) ^ normV v ^ i) - ((σ ^ i) x - (x : Ω) ^ normV v ^ i) := by
      ring
    rw [e]
    exact lt_of_le_of_lt (A.valuation.map_sub _ _) (max_lt h1 h2)
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · rintro τ ⟨h1, h2⟩
      exact ⟨h1, fun x hx => h2 x (Finset.mem_union_left _ hx)⟩
    · rintro τ ⟨h1, h2⟩
      exact ⟨h1, fun x hx => h2 x (Finset.mem_union_right _ hx)⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCne
    (fun S => (hCcl S).isCompact) hCcl
  rw [Set.mem_iInter] at hτ
  have hτCl : τ ∈ Cl := (hτ ∅).1
  have hτD := hClD hτCl
  have hτx : ∀ x : A, A.valuation (g x - τ x) < 1 := fun x => (hτ {x}).2 x (Finset.mem_singleton_self x)
  have hι : τ⁻¹ * g ∈ Ine (F := K) A := by
    show τ⁻¹ * g ∈ Inertia A
    refine ⟨(Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hτD) hg, fun x hx => ?_⟩
    have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    have e : (τ⁻¹ * g) x - x = τ⁻¹ (g x - τ x) := by
      rw [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [e, valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hτD)]
    exact hτx ⟨x, hxA⟩
  have e : g = τ * (τ⁻¹ * g) := by group
  rw [e]
  exact H.mul_mem (hClH hτCl) (hI hι)
