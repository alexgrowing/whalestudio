import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneTau
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem rat_pow {l : ℕ} (hl : Odd l) (a : ℚˣ) (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), (l : ℤ) ∣ Kum.ordv v a) :
    ∃ y : ℚ, (a : ℚ) = y ^ l := by
  have hl0 : l ≠ 0 := hl.pos.ne'
  have h1 := (Kum.radClKer ℚ ∅ l hl0 a fun v _ => h v).1 (by
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
    haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
      (@Fintype.card_le_one_iff_subsingleton _ (_)).1 (card_classGroup_eq_one (R := 𝓞 ℚ)).le
    rw [Subsingleton.elim (Kum.radCl l a) 1]; exact one_mem _)
  obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h1
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (u : ℚ) = 1 := fun v => hu v (by simp)
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (u : ℚ) fun v => (hv v).le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (u : ℚ)⁻¹ fun v => by
    rw [map_inv₀, hv v, inv_one]
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, hx, hy, map_one, mul_inv_cancel₀ u.ne_zero]
  have h2 : Rat.ringOfIntegersEquiv x * Rat.ringOfIntegersEquiv y = 1 := by rw [← map_mul, hxy, map_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with e | e
  · have : x = 1 := Rat.ringOfIntegersEquiv.injective (by rw [e, map_one])
    exact ⟨b, by simp [← hx, this]⟩
  · have : x = -1 := Rat.ringOfIntegersEquiv.injective (by rw [e, map_neg, map_one])
    exact ⟨-b, by simp [← hx, this, hl.neg_pow]⟩

private theorem rat_place (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ q : ℕ, q.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ w.asIdeal → w = v := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, fun w hw => ?_⟩
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  refine (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
    (Rat.HeightOneSpectrum.prime_natGenerator v)).1 ?_
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hw
  simpa using this

private theorem kum {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (hl : Odd l)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ l) (η z : G ℚ Ω → ZMod l) (hη : ∀ g : G ℚ Ω, g ζ = ζ ^ (η g).val)
    (hz : IsLocallyConstant z) (hc : ∀ g h, z (g * h) = z g + η g * z h)
    (hi : ∀ q : ℕ, q.Prime → ∃ A : ValuationSubring Ω, Over A q ∧ ∀ g ∈ Ine (F := ℚ) A, z g = 0)
    (t : G ℚ Ω) (ht : η t ≠ 1) (h0 : z t = 0) (g : G ℚ Ω) : z g = 0 := by
  obtain ⟨β, a, ha, hβ⟩ := Kum.radExists ℚ Ω l ζ η z hζ hη hz hc
  obtain ⟨y, hy⟩ := rat_pow hl a fun v => by
    obtain ⟨q, hq, hv⟩ := rat_place v
    obtain ⟨A, hA, hA'⟩ := hi q hq
    obtain ⟨w, hw, -, hw'⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.1 A q hq hA
    obtain rfl := hv w hw'
    exact Kum.dvdOfIne ℚ Ω l A w β a hw ha fun g hg => by rw [hβ, hA' g hg, ZMod.val_zero, pow_zero, one_mul]
  have hl0 : l ≠ 0 := hl.pos.ne'
  have hy0 : algebraMap ℚ Ω y ≠ 0 := by
    rw [map_ne_zero]; rintro rfl
    exact a.ne_zero (by rw [hy, zero_pow hl0])
  have h1 : (β / algebraMap ℚ Ω y) ^ l = 1 := by
    rw [div_pow, ha, hy, map_pow, div_self (pow_ne_zero _ hy0)]
  obtain ⟨j, hj, hj'⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hb : β = ζ ^ j * algebraMap ℚ Ω y := by rw [hj', div_mul_cancel₀ _ hy0]
  have key : ∀ g : G ℚ Ω, η g * j = z g + j := fun g => by
    have h2 := hβ g
    rw [hb, map_mul, map_pow, hη, AlgEquiv.commutes, ← mul_assoc, ← pow_mul, ← pow_add] at h2
    have h3 := mul_right_cancel₀ hy0 h2
    rw [pow_eq_pow_mod _ hζ.pow_eq_one, pow_eq_pow_mod (_ + _) hζ.pow_eq_one] at h3
    have h4 := hζ.pow_inj (Nat.mod_lt _ hl.pos) (Nat.mod_lt _ hl.pos) h3
    have h5 := (ZMod.natCast_eq_natCast_iff' _ _ l).2 h4
    simpa using h5
  have hj0 : (j : ZMod l) = 0 := by
    have h2 := key t
    rw [h0, zero_add] at h2
    by_contra hne
    exact ht (mul_right_cancel₀ hne (by rw [h2, one_mul]))
  simpa [hj0] using (key g).symm

private theorem cyc_nat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (g : G ℚ Ω) :
    ∃ n : ℕ, (∀ x : Ω, x ^ l = 1 → g x = x ^ n) ∧ (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  refine ⟨(PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val, fun x hx =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) x (by rwa [pow_one]), ?_⟩
  rw [← Ideal.mem_span_singleton, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, ZMod.natCast_zmod_val, sub_self]

private theorem l_mem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) := by
    rw [IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[l])
      (IsLocalRing.maximalIdeal O)), PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using h

private theorem sep' (l : ℕ) [Fact l.Prime] {V : Type} [AddCommGroup V] [Module (ZMod l) V] (v : V)
    (hv : ∀ f : V →+ ZMod l, f v = 0) : v = 0 :=
  (Module.forall_dual_apply_eq_zero_iff (ZMod l) v).1 fun f => hv f.toAddMonoidHom

private theorem sep (l : ℕ) [Fact l.Prime] {V : Type} [AddCommGroup V] (h : ∀ v : V, l • v = 0) (v : V)
    (hv : ∀ f : V →+ ZMod l, f v = 0) : v = 0 :=
  @sep' l _ V _ (AddCommGroup.zmodModule h) v hv

private theorem sht_pi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (hl : Odd l)
    {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (α : G ℚ Ω →* Oˣ) (π : O) (hπ : π ∣ (l : O))
    (n : G ℚ Ω → ℕ) (hn : ∀ (g : G ℚ Ω) (x : Ω), x ^ l = 1 → g x = x ^ n g) (hα : ∀ g, π ∣ (α g : O) - n g)
    (A₀ : ValuationSubring Ω) (hA₀ : Over A₀ l) (t : G ℚ Ω) (ht : t ∈ Ine (F := ℚ) A₀) (ht1 : (n t : ZMod l) ≠ 1)
    (hu : IsUnit ((α t : O) - 1)) (a : O) (c : G ℚ Ω → W) (hc : c ∈ ShT W α t l a) (h0 : π • c = 0) : c = 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨⟨h1, h2⟩, h3, -, h4, h5⟩ := hc
  obtain ⟨m, -, hm⟩ := h5 A₀ hA₀
  have hm0 : m = 0 := by
    have := hm t ht.1
    rw [h3] at this
    exact hu.smul_left_cancel.1 (by rw [sub_smul, one_smul, ← this, smul_zero])
  let V := Submodule.torsionBy O W π
  have kill : ∀ y : O, π ∣ y → ∀ v : V, y • v = 0 := by
    rintro _ ⟨y, rfl⟩ v
    rw [mul_comm, mul_smul, Submodule.smul_torsionBy, smul_zero]
  let c' : G ℚ Ω → V := fun g => ⟨c g, congrFun h0 g⟩
  have hlc : IsLocallyConstant c' := IsLocallyConstant.desc c' Subtype.val h1 Subtype.val_injective
  have hcc : ∀ g h, c' (g * h) = c' g + n g • c' h := fun g h => by
    have e := kill _ (hα g) (c' h)
    rw [sub_smul, sub_eq_zero, Nat.cast_smul_eq_nsmul] at e
    rw [← e]
    exact Subtype.ext (h2 g h)
  funext g
  refine congrArg Subtype.val (sep l (fun v => by rw [← Nat.cast_smul_eq_nsmul O, kill _ hπ]) (c' g) fun f => ?_)
  have z0 : ∀ g, c g = 0 → f (c' g) = 0 := fun g hg => by rw [show c' g = 0 from Subtype.ext hg, map_zero]
  refine kum hl hζ (fun g => (n g : ZMod l)) (fun g => f (c' g)) (fun g => ?_) (hlc.comp f) (fun g h => ?_)
    (fun q hq => ?_) t ht1 (z0 t h3) g
  · rw [hn g ζ hζ.pow_eq_one, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ.pow_eq_one]
  · rw [hcc, map_add, map_nsmul, nsmul_eq_mul]
  · by_cases e : q = l
    · exact ⟨A₀, e ▸ hA₀, fun g hg => z0 g (by rw [hm g hg.1, hm0, smul_zero, sub_zero])⟩
    · obtain ⟨A, hA⟩ := (placeBasic Ω).1 q hq
      exact ⟨A, hA, fun g hg => z0 g (h4 A ((placeBasic Ω).2.2.2.1 A q l ((Nat.coprime_primes hq hp).2 e) hA) g hg)⟩

theorem UpperTheory.V.ML.exc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], l ≠ 2 → ∀ α : G ℚ Ω →* Oˣ, (∀ g, ¬ IsUnit ((α g : O) - (chiO ℚ Ω l O g : O))) →
    (∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1) → ShaU (twist₂ l α) l (⊤ : Subgroup (G ℚ Ω)) = ⊥ := by
  intro Ω _ _ _ l _ O _ _ _ _ _ hl2 α hα hun
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : l.Prime := Fact.out
  have hl : Odd l := hp.odd_of_ne_two hl2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ π ∣ y := fun y => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hπl : π ∣ (l : O) := (hmax _).1 (l_mem l O)
  choose n hn hn' using cyc_nat (Ω := Ω) l
  have hαn : ∀ g, π ∣ (α g : O) - n g := fun g => by
    have e1 : π ∣ (α g : O) - (chiO ℚ Ω l O g : O) := (hmax _).1 (hα g)
    have e2 := map_dvd (algebraMap ℤ_[l] O) (hn' g)
    rw [map_natCast, map_sub, map_natCast] at e2
    have := dvd_add e1 (hπl.trans e2)
    rwa [show (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cycZ ℚ Ω l g : ℤ_[l]) from rfl, sub_add_sub_cancel] at this
  obtain ⟨A₀, hA₀⟩ := (placeBasic Ω).1 l hp
  obtain ⟨t, ht, htl⟩ := (ineTau Ω l hp).1 A₀ hA₀ (-1)
  have ht1 : (n t : ZMod l) ≠ 1 := fun e => by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
    have h3 := (hn t ζ hζ.pow_eq_one).symm.trans (htl ζ hζ.pow_eq_one)
    rw [pow_eq_pow_mod _ hζ.pow_eq_one] at h3
    have h4 := hζ.pow_inj (Nat.mod_lt _ hl.pos) (ZMod.val_lt _) h3
    rw [← ZMod.val_natCast, e] at h4
    have h5 := ZMod.val_injective l h4
    haveI : Fact (2 < l) := ⟨lt_of_le_of_ne hp.two_le hl2.symm⟩
    exact ZMod.neg_one_ne_one (by simpa using h5.symm)
  have hu : IsUnit ((α t : O) - 1) := by
    by_contra hnu
    have e1 : π ∣ (α t : O) - 1 := (hmax _).1 hnu
    have e2 : π ∣ (n t : O) - 1 := by simpa using dvd_sub e1 (hαn t)
    have e3 : IsUnit ((n t : ℤ_[l]) - 1) := by
      by_contra h
      have h' : (n t : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
        rw [PadicInt.ker_toZMod]; exact h
      exact ht1 (by simpa [sub_eq_zero] using h')
    have e4 := e3.map (algebraMap ℤ_[l] O)
    rw [map_sub, map_natCast, map_one] at e4
    exact hπ.not_isUnit (isUnit_of_dvd_unit e2 e4)
  have key := shaToShT Ω l O α t hu l hp.ne_zero hun (fun A h h' => absurd h h') 0 fun a ha => by
    have hb : ShT (QO l O) α t l a = ⊥ := by
      have ind : ∀ (k : ℕ), ∀ c ∈ ShT (QO l O) α t l a, π ^ k • c = 0 → c = 0 := fun k => by
        induction k with
        | zero => intro c _ h; simpa using h
        | succ k ih =>
          intro c hc h
          exact ih c hc (sht_pi hl α π hπl n hn hαn A₀ hA₀ t ht ht1 hu a _ (Submodule.smul_mem _ _ hc)
            (by rw [← mul_smul, ← pow_succ', h]))
      obtain ⟨k, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine (Submodule.eq_bot_iff _).2 fun c hc => ind k c hc ?_
      have h1 : a • c = 0 := funext hc.2.2.1
      rw [e, mul_smul] at h1
      exact u.isUnit.smul_left_cancel.1 (by rw [h1, smul_zero])
    rw [hb, Module.length_bot]
  exact Submodule.subsingleton_iff_eq_bot.1 (Module.length_eq_zero_iff.1 (nonpos_iff_eq_zero.1 key))
