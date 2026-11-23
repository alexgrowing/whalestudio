import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RayChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.FrobDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.ExtIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.QuadFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algClosure (K : IntermediateField ℚ Ω) : IsAlgClosure K Ω := by
  rw [isAlgClosure_iff]
  exact ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem exists_prim {k : Type} [Field k] {N : ℕ} (hN : 1 ≤ N) (φ : G ℚ Ω →* kˣ) (hφ : Af.KillsMu N φ) :
    ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter k M), χ.IsPrimitive ∧ φ = Chr.dirG ℚ Ω χ := by
  haveI : NeZero N := ⟨by omega⟩
  unfold Af.KillsMu at hφ
  have hsurj := (Chr.clsOnto Ω N).1
  have hker : (Chr.cls ℚ Ω N).ker ≤ φ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    apply hφ σ
    intro ζ hζ
    rw [Chr.cls_spec N σ ζ hζ, hσ, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
      pow_one]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (ZMod N)ˣ →* kˣ, ψ.comp (Chr.cls ℚ Ω N) = φ :=
    ⟨_, MonoidHom.liftOfRightInverse_comp _ _ (Function.rightInverse_surjInv hsurj) ⟨φ, hker⟩⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : DirichletCharacter k N, χ.toUnitHom = ψ :=
    ⟨MulChar.ofUnitHom ψ, by simp [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq]⟩
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine ⟨χ.conductor, inferInstance, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, ?_⟩
  have h2 : χ.toUnitHom =
      χ.primitiveCharacter.toUnitHom.comp (ZMod.unitsMap χ.conductor_dvd_level) := by
    conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_toUnitHom]
  have h3 := (Chr.clsFacts ℚ Ω N).2.1 χ.conductor χ.conductor_dvd_level
  unfold Chr.dirG
  rw [← hψ, ← hχ, h2, MonoidHom.comp_assoc, h3]

private theorem ramified {k : Type} [Field k] {M : ℕ} [NeZero M] {χ : DirichletCharacter k M} (hχ : χ.IsPrimitive)
    {A : ValuationSubring Ω} (hA : A.valuation (M : Ω) < 1) : ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω χ).ker := by
  intro hle
  have hM0 : M ≠ 0 := NeZero.ne M
  obtain ⟨p, hp, hpA⟩ := ((Chr.placesQ Ω).2.1 A M hM0).1 hA
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpM : p ∣ M := Nat.dvd_of_mem_primeFactors hp
  have hc : HV.comp p χ = 1 := ((HV.compIne Ω M p hpp A hpA).2 k χ).2.mp hle
  have hc' : ∀ v, χ.toUnitHom (HV.proj p M v) = 1 := by
    intro v
    have h0 := (MulChar.ext_iff.mp hc) v
    unfold HV.comp at h0
    simp only [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.one_apply_coe] at h0
    exact Units.val_eq_one.mp h0
  have hfac : χ.FactorsThrough (M / p ^ M.factorization p) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd M p)]
    intro u hu
    rw [← (HV.projFacts M p hpp).2.2.2.2.2.1] at hu
    obtain ⟨v, rfl⟩ := hu
    exact hc' v
  have hle' : χ.conductor ≤ M / p ^ M.factorization p := Nat.sInf_le hfac
  rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hle'
  have hk : M.factorization p ≠ 0 := (hpp.factorization_pos_of_dvd hM0 hpM).ne'
  have hlt : M / p ^ M.factorization p < M :=
    Nat.div_lt_self (Nat.pos_of_ne_zero hM0) (Nat.one_lt_pow hk hpp.one_lt)
  omega

private theorem exists_cc : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, hσ⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    rw [eq_ratCast (algebraMap ℚ Ω) x]
    exact map_ratCast σ x), ?_⟩
  unfold IsCC
  unfold IsConjOm at hσ
  obtain ⟨j, hj⟩ := hσ
  exact ⟨j, fun x => hj x⟩

private theorem exists_hom {R : Type} [CommRing R] {M : ℕ} [NeZero M]
    (h : ∀ p ∈ M.primeFactors, ∀ n : ℕ, Nonempty (R →+* ZMod (p ^ n))) : Nonempty (R →+* ZMod M) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  exact ⟨((ZMod.equivPi M hM).symm : _ →+* ZMod M).comp
    (Pi.ringHom fun p : M.primeFactors => (h p p.2 (M.factorization p)).some)⟩

private theorem unit_of_coprime {R : Type} [CommRing R] {M : ℕ} (φ : R →+* ZMod M) {a : R}
    (h : IsCoprime (Ideal.span {a}) (Ideal.span {(M : R)})) : IsUnit (φ a) := by
  have h1 : (1 : R) ∈ Ideal.span {a} ⊔ Ideal.span {(M : R)} := by
    rw [Ideal.isCoprime_iff_sup_eq.mp h]
    exact Submodule.mem_top
  rw [← Ideal.span_insert, Ideal.mem_span_pair] at h1
  obtain ⟨x, z, hxz⟩ := h1
  have h2 := congrArg φ hxz
  simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, mul_zero, add_zero, map_one] at h2
  exact isUnit_iff_exists_inv'.mpr ⟨_, h2⟩

private theorem coprime_of_not_mem {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) {a : R}
    (h : a ∉ w.asIdeal) : IsCoprime w.asIdeal (Ideal.span {a}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  have hmax : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  by_contra hne
  apply h
  have heq := hmax.eq_of_le hne (le_sup_left : w.asIdeal ≤ w.asIdeal ⊔ Ideal.span {a})
  rw [heq]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)

private theorem cls_frob {M q : ℕ} [NeZero M] {A : ValuationSubring Ω} (hA : ¬ A.valuation (M : Ω) < 1) {σ : G ℚ Ω}
    (h : IsFrob (F := ℚ) A q σ) (hq : IsUnit (q : ZMod M)) : ((Chr.cls ℚ Ω M σ : (ZMod M)ˣ) : ZMod M) = q := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A q M σ h hA
  have h2 := (Chr.clsFacts ℚ Ω M).2.2.1 σ hq.unit fun ζ hζ => by
    rw [h1 ζ hζ, hq.unit_spec, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  rw [h2, hq.unit_spec]

private theorem primeTo {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [CommGroup C]
    (κ : Γ →* C) (hκ : IsOpen (κ.ker : Set Γ)) {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m) :
    ∃ j m' : ℕ, l.Coprime m' ∧ (κ ^ j) ^ m' = 1 ∧ j ≡ 1 [MOD m] := by
  haveI : Finite (Γ ⧸ κ.ker) := Subgroup.quotient_finite_of_isOpen _ hκ
  have hn : κ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨a, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.ne_one
  have hco : (l ^ a).Coprime m := Nat.Coprime.pow_left a hm
  obtain ⟨j, hj0, hj1⟩ := Nat.chineseRemainder hco 0 1
  refine ⟨j, n', (Nat.Prime.coprime_iff_not_dvd hl).2 hn', ?_, hj1⟩
  obtain ⟨t, ht⟩ : l ^ a ∣ j := (Nat.modEq_zero_iff_dvd).1 hj0
  have hjn : j * n' = κ.ker.index * t := by rw [ht, hnn]; ring
  rw [← pow_mul, hjn]
  ext g
  rw [MonoidHom.one_apply, pow_mul]
  simp only [MonoidHom.pow_apply]
  rw [← map_pow, (κ.mem_ker).1 (Subgroup.pow_index_mem _ g), one_pow]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.Tw.kap0 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → (∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup) → ∀ (η : G ℚ Ω →* (PadicAlgCl l)ˣ) (N m : ℕ), 1 ≤ N → Af.KillsMu N η → l.Coprime m → η ^ m = 1 → (∀ c, IsCC c → η c = 1) → (∀ A : ValuationSubring Ω, Ine (F := ℚ) A ≤ η.ker ∨ Dec (F := ℚ) A ≤ K.fixingSubgroup) → ∃ (κ : G K Ω →* (PadicAlgCl l)ˣ) (m' : ℕ), IsOpen (κ.ker : Set (G K Ω)) ∧ l.Coprime m' ∧ κ ^ m' = 1 ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → κ s * κ s' = η (resQ K s)) ∧ ∀ A : ValuationSubring Ω, Ine (F := ℚ) A ≤ η.ker → Ine (F := K) A ≤ κ.ker := by
  intro Ω _ _ _ l _ hl2 K _ _ h2 h2split η N m hN hη hm hηm hcc hram
  classical
  haveI : IsAlgClosure K Ω := algClosure K
  obtain ⟨M, _, χ, hχ, rfl⟩ := exists_prim hN η hη
  have hM0 : M ≠ 0 := NeZero.ne M
  obtain ⟨τ, hτc, hτn, hτf, hsp, hun⟩ := Tw.quadFacts Ω l hl2 K h2
  have hρ : Nonempty (𝓞 K →+* ZMod M) := by
    apply exists_hom
    intro p hp n
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 p hpp
    have hAM : A.valuation (M : Ω) < 1 := ((Chr.placesQ Ω).2.1 A M hM0).2 ⟨p, hp, hA⟩
    have hdec : Dec (F := ℚ) A ≤ K.fixingSubgroup := (hram A).resolve_left (ramified hχ hAM)
    obtain ⟨w, -, -, -, hφ⟩ := hsp p A hpp hA hdec
    obtain ⟨φ, -⟩ := hφ n
    exact ⟨φ⟩
  obtain ⟨ρ⟩ := hρ
  set 𝔪 : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with h𝔪def
  have h𝔪 : 𝔪 ≠ ⊥ := by
    rw [h𝔪def, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hM0
  have hρM : ∀ x ∈ 𝔪, ρ x = 0 := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_natCast, ZMod.natCast_self, mul_zero]
  let g : 𝓞 K → (PadicAlgCl l)ˣ := fun a => if h : IsUnit (ρ a) then χ.toUnitHom h.unit else 1
  have hg : ∀ a (h : IsUnit (ρ a)), ((g a : (PadicAlgCl l)ˣ) : PadicAlgCl l) = χ (ρ a) := by
    intro a h
    simp only [g, dif_pos h, MulChar.coe_toUnitHom, IsUnit.unit_spec]
  have hχm1 : χ (-1) = 1 := by
    obtain ⟨c0, hc0⟩ := exists_cc (Ω := Ω)
    have h1 := hcc c0 hc0
    have h2' : Chr.cls ℚ Ω M c0 = -1 := (Chr.clsFacts ℚ Ω M).2.2.2.1 c0 (by
      unfold IsConjOm
      unfold IsCC at hc0
      exact hc0)
    unfold Chr.dirG at h1
    rw [MonoidHom.comp_apply, h2'] at h1
    have h3 := congrArg Units.val h1
    rw [MulChar.coe_toUnitHom] at h3
    simpa using h3
  obtain ⟨f, hfmul, hfg⟩ := Tw.extIdeal K 𝔪 h𝔪 (PadicAlgCl l) g (by
    intro a b _ _ hca hcb
    have hua := unit_of_coprime ρ hca
    have hub := unit_of_coprime ρ hcb
    have hab : IsUnit (ρ (a * b)) := by rw [map_mul]; exact hua.mul hub
    apply Units.ext
    rw [Units.val_mul, hg _ hab, hg _ hua, hg _ hub, map_mul, map_mul]) (by
    intro u
    rcases hun h2split u with h | h
    · rw [h, Units.val_one]
      have h1 : IsUnit (ρ 1) := by rw [map_one]; exact isUnit_one
      apply Units.ext
      rw [hg _ h1, map_one, MulChar.map_one, Units.val_one]
    · rw [h, Units.val_neg, Units.val_one]
      have h1 : IsUnit (ρ (-1)) := by rw [map_neg, map_one]; exact isUnit_one.neg
      apply Units.ext
      rw [hg _ h1, map_neg, map_one, hχm1, Units.val_one])
  obtain ⟨κ0, hκopen, hκ⟩ := Tw.rayChar K Ω 𝔪 h𝔪 (PadicAlgCl l)ˣ f hfmul (by
    intro a ha0 ha1
    have hcop : IsCoprime (Ideal.span {a}) 𝔪 := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have h1 : (1 : 𝓞 K) = a - (a - 1) := by ring
      rw [h1]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
        (Ideal.mem_sup_right ha1)
    rw [hfg a ha0 hcop]
    have hρa : ρ a = 1 := by
      have h1 := hρM _ ha1
      rwa [map_sub, map_one, sub_eq_zero] at h1
    apply Units.ext
    rw [hg a (by rw [hρa]; exact isUnit_one), hρa, MulChar.map_one, Units.val_one])
  have key : ∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ →
      κ0 s * κ0 s' = Chr.dirG ℚ Ω χ (resQ K s) := by
    intro c hc
    have hci : c⁻¹ ∉ K.fixingSubgroup := fun h => hc (by simpa using K.fixingSubgroup.inv_mem h)
    let τK : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) τ
    have hlift : IsLift τK (c⁻¹).toRingEquiv := by
      have hext : ((c⁻¹).toRingEquiv.toRingHom.comp (algebraMap K Ω)) =
          (algebraMap K Ω).comp τK.toRingHom := by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
        exact hτc _ hci x
      unfold IsLift
      intro x
      exact RingHom.congr_fun hext x
    let Cg := conjGal hlift
    have hCg : ∀ s, resQ K (Cg s) = c * resQ K s * c⁻¹ := fun s => by
      ext x
      rfl
    have hFx : ∀ x, (κ0 * κ0.comp Cg * ((Chr.dirG ℚ Ω χ).comp (resQ K))⁻¹) x =
        κ0 x * κ0 (Cg x) * (Chr.dirG ℚ Ω χ (resQ K x))⁻¹ := fun x => rfl
    have hFopen : IsOpen ((κ0 * κ0.comp Cg * ((Chr.dirG ℚ Ω χ).comp (resQ K))⁻¹).ker :
        Set (G K Ω)) := by
      apply Subgroup.isOpen_mono (H₁ := κ0.ker ⊓ κ0.ker.comap Cg ⊓ (Chr.cls K Ω M).ker)
      · intro x hx
        obtain ⟨⟨h1, h2⟩, h3⟩ := hx
        have h1' : κ0 x = 1 := h1
        have h2' : κ0 (Cg x) = 1 := h2
        have h3' : Chr.cls K Ω M x = 1 := h3
        rw [MonoidHom.mem_ker]
        have h4 : Chr.cls ℚ Ω M (resQ K x) = 1 := by
          apply (Chr.clsFacts ℚ Ω M).2.2.1
          intro ζ hζ
          have h5 := Chr.cls_spec M x ζ hζ
          rw [h3'] at h5
          exact h5
        rw [hFx, h1', h2']
        unfold Chr.dirG
        rw [MonoidHom.comp_apply, h4, map_one, inv_one, mul_one, mul_one]
      · rw [Subgroup.coe_inf, Subgroup.coe_inf, Subgroup.coe_comap]
        exact (hκopen.inter (hκopen.preimage (continuous_conjGal hlift))).inter
          (Chr.clsFacts K Ω M).1
    have hclosed := Subgroup.isClosed_of_isOpen _ hFopen
    have hsub : {σ | ∃ w A, ¬w.asIdeal ∣ 𝔪 ∧ IsPlaceOver A w ∧ IsFrob A (normV w) σ} ⊆
        ((κ0 * κ0.comp Cg * ((Chr.dirG ℚ Ω χ).comp (resQ K))⁻¹).ker : Set (G K Ω)) := by
      rintro σ ⟨w, A, hw, hA, hfr⟩
      have hwM : (M : 𝓞 K) ∉ w.asIdeal := fun h => hw (Ideal.dvd_span_singleton.mpr h)
      obtain ⟨w', A', hw', hA', hfr'⟩ := hτf c hc σ (Cg σ) (hCg σ) w A hA hfr
      have hw'M : (M : 𝓞 K) ∉ w'.asIdeal := by
        rw [hw']
        intro h
        apply hwM
        obtain ⟨y, hy, hyM⟩ := (Ideal.mem_map_of_equiv τ _).mp h
        have hyM' : y = (M : 𝓞 K) := τ.injective (by rw [hyM, map_natCast])
        exact hyM' ▸ hy
      have hw'd : ¬ w'.asIdeal ∣ 𝔪 := fun h => hw'M (Ideal.dvd_span_singleton.mp h)
      have hκw := (hκ w hw A hA).2 σ hfr
      have hκw' := (hκ w' hw'd A' hA').2 (Cg σ) hfr'
      have hcw : IsCoprime w.asIdeal 𝔪 := coprime_of_not_mem w hwM
      have hcw' : IsCoprime w'.asIdeal 𝔪 := coprime_of_not_mem w' hw'M
      have hprod : w.asIdeal * w'.asIdeal =
          Ideal.span {((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)} := by
        rw [hw']
        exact hτn w.asIdeal
      have hcq : IsCoprime (Ideal.span {((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)}) 𝔪 := by
        rw [← hprod]
        exact hcw.mul_left hcw'
      have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K) ≠ 0 := by
        intro h
        rw [h, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mul_eq_bot] at hprod
        rcases hprod with h' | h'
        · exact w.ne_bot h'
        · exact w'.ne_bot h'
      have hfq : f w.asIdeal * f w'.asIdeal = g ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K) := by
        rw [← hfmul _ _ w.ne_bot w'.ne_bot hcw hcw', hprod, hfg _ hq0 hcq]
      have huq : IsUnit (ρ ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)) := unit_of_coprime ρ hcq
      have hqM : IsUnit ((Ideal.absNorm w.asIdeal : ℕ) : ZMod M) := by
        rwa [map_natCast] at huq
      have hnorm : normV w = Ideal.absNorm w.asIdeal := by
        unfold normV
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have hAM : ¬ A.valuation (M : Ω) < 1 := by
        intro h
        apply hwM
        unfold IsPlaceOver at hA
        exact (hA (M : 𝓞 K)).mp (by simpa using h)
      have hfrQ : IsFrob (F := ℚ) A (Ideal.absNorm w.asIdeal) (resQ K σ) := by
        rw [← hnorm]
        unfold IsFrob at hfr ⊢
        exact hfr
      have hcls := cls_frob hAM hfrQ hqM
      show σ ∈ (κ0 * κ0.comp Cg * ((Chr.dirG ℚ Ω χ).comp (resQ K))⁻¹).ker
      rw [MonoidHom.mem_ker, hFx, hκw, hκw', hfq, mul_inv_eq_one]
      apply Units.ext
      rw [hg _ huq]
      unfold Chr.dirG
      rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom, hcls, map_natCast]
    intro s s' hs'
    have hs'' : s' = Cg s := by
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun g : G ℚ Ω => g x) (hs'.trans (hCg s).symm)
    subst hs''
    have hmem : s ∈ (κ0 * κ0.comp Cg * ((Chr.dirG ℚ Ω χ).comp (resQ K))⁻¹).ker :=
      closure_minimal hsub hclosed ((Tw.frobDense K Ω 𝔪 h𝔪).closure_eq ▸ Set.mem_univ s)
    rw [MonoidHom.mem_ker, hFx, mul_inv_eq_one] at hmem
    exact hmem
  obtain ⟨j, m', hm', hκm, hj⟩ := primeTo κ0 hκopen (Fact.out : l.Prime) hm
  have kerle : κ0.ker ≤ (κ0 ^ j).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    simp only [MonoidHom.pow_apply, hx, one_pow]
  refine ⟨κ0 ^ j, m', Subgroup.isOpen_mono kerle hκopen, hm', hκm, ?_, ?_⟩
  · intro c hc s s' hs'
    have h0 := key c hc s s' hs'
    have hpow : ∀ x : G ℚ Ω, Chr.dirG ℚ Ω χ x ^ j = Chr.dirG ℚ Ω χ x := by
      intro x
      have hxm : Chr.dirG ℚ Ω χ x ^ m = 1 := by
        have h1 := congrArg (fun φ : G ℚ Ω →* (PadicAlgCl l)ˣ => φ x) hηm
        simpa using h1
      rw [pow_eq_pow_mod j hxm, show j % m = 1 % m from hj, ← pow_eq_pow_mod 1 hxm, pow_one]
    simp only [MonoidHom.pow_apply]
    rw [← mul_pow, h0, hpow]
  · intro A hA
    rcases eq_or_ne A ⊤ with hT | hT
    · rw [((Base.places K Ω l A).2.1 hT).1]
      exact bot_le
    · obtain ⟨v, hv⟩ := (Base.places K Ω l A).1 hT
      by_cases hvM : (M : 𝓞 K) ∈ v.asIdeal
      · exfalso
        have hAM : A.valuation (M : Ω) < 1 := by
          unfold IsPlaceOver at hv
          simpa using (hv (M : 𝓞 K)).mpr hvM
        exact ramified hχ hAM hA
      · have hd : ¬ v.asIdeal ∣ 𝔪 := fun h => hvM (Ideal.dvd_span_singleton.mp h)
        exact le_trans (hκ v hd A hv).1 kerle
