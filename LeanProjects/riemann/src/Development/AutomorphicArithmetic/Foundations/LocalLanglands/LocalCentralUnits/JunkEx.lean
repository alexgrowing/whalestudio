import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsUnitResidueLogarithmOfRootsOfUnity
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsAdicCompletionRingEquivExtendingOfStable
import Development.AutomorphicArithmetic.WhittakerHecke.CardResidueFieldAdicCompletionIntegersEqAbsNorm
import Development.AutomorphicArithmetic.WhittakerHecke.ContinuousInertiaRestrictionOfCompat
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsNumberFieldExtensionPlaceFrobeniusDegree
import Development.AutomorphicArithmetic.WhittakerHecke.TameInertiaCharacterFrobeniusConjEqPow
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLMemWeil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem exists_frobAut (K : Type) [Field K] [Finite K] (q n : ℕ) (hq : 1 < q) (hn : 0 < n)
    (hcard : Nat.card K = q ^ n) : ∃ f : RingAut K, (∀ x, f x = x ^ q) ∧ orderOf f = n := by
  classical
  letI := Fintype.ofFinite K
  obtain ⟨p, hpc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar K p := ExpChar.prime hp
  have hc : Fintype.card K = q ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hd : q ∣ p ^ (k : ℕ) := by
    rw [← hk, hc]; exact dvd_pow_self q hn.ne'
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
  let f0 : K →+* K := iterateFrobenius K p j
  have hinj : Function.Injective f0 := f0.injective
  let f : RingAut K := RingEquiv.ofBijective f0 (Finite.injective_iff_bijective.1 hinj)
  have hf : ∀ x, f x = x ^ p ^ j := fun x => iterateFrobenius_def p j x
  have hpow : ∀ (m : ℕ) (x : K), (f ^ m) x = x ^ (p ^ j) ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', RingAut.mul_apply, ih, hf, ← pow_mul, ← pow_succ]
  refine ⟨f, hf, (orderOf_eq_iff hn).2 ⟨?_, fun m hmn hm0 hone => ?_⟩⟩
  · ext x
    rw [hpow, ← hc, FiniteField.pow_card]
    rfl
  · obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hob : orderOf b = (p ^ j) ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, Fintype.card_units, hc]
    have hq1 : 1 ≤ (p ^ j) ^ m := Nat.one_le_pow _ _ (by omega)
    have h1 : (b : K) ^ (p ^ j) ^ m = b := by
      rw [← hpow, hone]; rfl
    have h2 : b ^ ((p ^ j) ^ m - 1) = 1 := by
      have h3 : b ^ (p ^ j) ^ m = b := Units.ext (by simpa using h1)
      have h4 : b ^ ((p ^ j) ^ m - 1) * b = 1 * b := by
        rw [← pow_succ, Nat.sub_add_cancel hq1, one_mul, h3]
      exact mul_right_cancel h4
    have hdv := orderOf_dvd_of_pow_eq_one h2
    rw [hob] at hdv
    have hlt : (p ^ j) ^ m < (p ^ j) ^ n := Nat.pow_lt_pow_right hq hmn
    have h2m : 2 ≤ (p ^ j) ^ m := le_trans hq (Nat.le_self_pow hm0.ne' _)
    have := Nat.le_of_dvd (by omega) hdv
    omega

private theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

private theorem exp_neg_one_le {γ : WithZero (Multiplicative ℤ)} (h : ¬ γ ≤ WithZero.exp (-2 : ℤ)) :
    WithZero.exp (-1 : ℤ) ≤ γ := by
  have h0 : γ ≠ 0 := by rintro rfl; exact h zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [WithZero.exp_le_exp] at h ⊢
  omega

private theorem le_val_of_not_mem_sq {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) (c : 𝓞 L)
    (hc1 : c ∈ u.asIdeal) (hc2 : c ∉ u.asIdeal ^ 2) (x : u.adicCompletion L) (hx : Valued.v x < 1) :
    Valued.v x ≤ Valued.v (algebraMap L (u.adicCompletion L) (c : L)) := by
  have e : (Valued.v (algebraMap L (u.adicCompletion L) (c : L)) : WithZero (Multiplicative ℤ)) = u.intValuation c :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) u (c : L)).trans
      (HeightOneSpectrum.valuation_of_algebraMap u c)
  rw [e]
  refine (le_exp_neg_one hx).trans (exp_neg_one_le fun h2 => hc2 ?_)
  exact_mod_cast (u.intValuation_le_pow_iff_mem c 2).1 (by simpa using h2)

private theorem junkData (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : RingAut K) (π : Ine (F := E) A →* Multiplicative K),
      Nat.card K = normV w ^ n ∧ orderOf f = n ∧ Function.Surjective π ∧ IsOpen (π.ker : Set (Ine (F := E) A)) ∧
      ∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
        π t' = Multiplicative.ofAdd (f (Multiplicative.toAdd (π t))) := by
  classical
  obtain ⟨c, hcw, hc2⟩ : ∃ c : 𝓞 E, c ∈ w.asIdeal ∧ c ∉ w.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl)
  have hφ : IsFrob A (normV w) (frob h : G E Ω) := isFrob_frob
  obtain ⟨L, _, _, _, _, _, _, u, hu, s, hs, hfix, hcu, hN⟩ := UpperTheory.exists_numberField_extension_place_frobenius_degree E Ω A w h n hn _ hφ c hc2
  obtain ⟨a, ha, -⟩ := UpperTheory.Zero.LLC.artEx L Ω A u hu
  have hsu : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal := by
    intro x
    rw [← hu, ← hu x]
    have e : algebraMap L Ω ((RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) x : 𝓞 L) : L) =
        (frob h : G E Ω) (algebraMap L Ω (x : L)) := (hs _).symm
    rw [e]
    exact valuation_apply_lt_one_iff hφ.1 _
  obtain ⟨i, hic, hil, hiv⟩ := UpperTheory.exists_adicCompletion_ringEquiv_extending_of_stable u s.toRingEquiv hsu

  have hcL1 : algebraMap (𝓞 E) (𝓞 L) c ∈ u.asIdeal := by
    rw [← hu]
    have e : algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) c : 𝓞 L) : L) = algebraMap E Ω (c : E) :=
      (IsScalarTower.algebraMap_apply E L Ω (c : E)).symm
    rw [e]
    exact (h c).2 hcw
  set cL : 𝓞 L := algebraMap (𝓞 E) (𝓞 L) c with hcL
  set ϖ : u.adicCompletion L := algebraMap L (u.adicCompletion L) (cL : L) with hϖdef
  have hcL0 : cL ≠ 0 := fun h0 => hcu (by rw [h0]; exact zero_mem _)
  have hϖ0 : ϖ ≠ 0 := by
    rw [hϖdef, Ne, map_eq_zero]
    exact_mod_cast hcL0
  have hϖ1 : Valued.v ϖ < 1 := DiscreteGroups.sglob.DzType.val_alg_lt_one_of_mem cL hcL1
  have hϖ : ∀ x : u.adicCompletion L, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ :=
    le_val_of_not_mem_sq u cL hcL1 hcu
  let O : ValuationSubring (u.adicCompletion L) := (Valued.v : Valuation (u.adicCompletion L) _).valuationSubring
  let K : Type := IsLocalRing.ResidueField O
  let ρ : O →+* K := IsLocalRing.residue O
  have hcard : Nat.card K = normV w ^ n := (UpperTheory.card_residueField_adicCompletionIntegers_eq_absNorm u).trans hN
  have hq1 : 1 < normV w := one_lt_normV w
  have hQ : 4 ≤ normV w ^ n := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ normV w ^ 2 := Nat.pow_le_pow_left hq1 2
      _ ≤ normV w ^ n := Nat.pow_le_pow_right (by omega) hn
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  letI := Fintype.ofFinite K
  have hcardF : Fintype.card K = normV w ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hρ0 : ∀ x : O, ρ x = 0 ↔ Valued.v (x : u.adicCompletion L) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.symm
  have hNz : ∀ z : K, z ≠ 0 → z ^ (normV w ^ n - 1) = 1 := fun z hz => by
    rw [← hcardF]; exact FiniteField.pow_card_sub_one_eq_one z hz
  have hNK : (((normV w ^ n - 1 : ℕ)) : K) = -1 := by
    have h0 : ((normV w ^ n : ℕ) : K) = 0 := by rw [← hcardF]; exact Nat.cast_card_eq_zero K
    rw [Nat.cast_sub (by omega), h0, Nat.cast_one, zero_sub]
  obtain ⟨abelian₂, hadd, hLs, hL0, hLi⟩ := UpperTheory.exists_unit_residue_logarithm_of_roots_of_unity (K := K) Valued.v ϖ hϖ0 hϖ1 hϖ ρ
    IsLocalRing.residue_surjective hρ0 (normV w ^ n - 1) (by omega) hNz hNK
  obtain ⟨f, hfx, hfo⟩ := exists_frobAut K (normV w) n hq1 (by omega) hcard

  have hρeq : ∀ x y : O, Valued.v ((x : u.adicCompletion L) - y) < 1 → ρ x = ρ y := by
    intro x y hxy
    rw [← sub_eq_zero, ← map_sub]
    exact (hρ0 _).2 (by simpa using hxy)
  have hρi : ∀ x y : O, (y : u.adicCompletion L) = i x →
      ρ y = f (ρ x) := by
    intro x y hyx
    obtain ⟨z, hz⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl u (x : u.adicCompletion L) x.2
    let Z : O := ⟨algebraMap L (u.adicCompletion L) (z : L), DiscreteGroups.sglob.DzType.val_le_one_int u z⟩
    have h1 : ρ x = ρ Z := hρeq _ _ hz
    have h2 : f (ρ x) = ρ (Z ^ normV w) := by
      rw [h1, map_pow]
      exact hfx _
    rw [h2]
    apply hρeq
    let z' : 𝓞 L := RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) z - z ^ normV w
    have hz' : z' ∈ u.asIdeal := by
      rw [← hu]
      have e : algebraMap L Ω (z' : L) = (frob h : G E Ω) (algebraMap L Ω (z : L)) - (algebraMap L Ω (z : L)) ^ normV w := by
        rw [hs]
        simp [z']
      rw [e]
      exact hφ.2 _ (GlobalTheory.UnrCycExt.val_le_one_of_int A z)
    have e : (y : u.adicCompletion L) - ((Z ^ normV w : O) : u.adicCompletion L) =
        i ((x : u.adicCompletion L) - algebraMap L _ (z : L)) + algebraMap L _ (z' : L) := by
      rw [hyx, map_sub, hil]
      simp [z', Z]
    rw [e]
    refine Valuation.map_add_lt _ ?_ (DiscreteGroups.sglob.DzType.val_alg_lt_one_of_mem z' hz')
    rw [hiv]
    exact hz

  have hfixA : ∀ t : Ine (F := E) A, ∀ x : L, (t : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun t => hfix t t.2
  let ι₀ : Ine (F := E) A → G L Ω := fun t => { (t : G E Ω).toRingEquiv with commutes' := hfixA t }
  have hι₀ : ∀ (t : Ine (F := E) A) (x : Ω), ι₀ t x = (t : G E Ω) x := fun _ _ => rfl
  have hι₀m : ∀ t, ι₀ t ∈ Ine (F := L) A := fun t =>
    ⟨GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec t.2.1 x, fun x hx => t.2.2 x hx⟩
  let ι : Ine (F := E) A →* Ine (F := L) A := MonoidHom.mk' (fun t => ⟨ι₀ t, hι₀m t⟩) fun t t' => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  have hι : ∀ (t : Ine (F := E) A) (x : Ω), (ι t : G L Ω) x = (t : G E Ω) x := fun _ _ => rfl
  have hιs : ∀ t₁ : Ine (F := L) A, ∃ t : Ine (F := E) A, ι t = t₁ := by
    intro t₁
    have hd : AlgEquiv.restrictScalars E (t₁ : G L Ω) ∈ Ine (F := E) A :=
      ⟨GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec t₁.2.1 x, fun x hx => t₁.2.2 x hx⟩
    exact ⟨⟨_, hd⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩
  have hval : ∀ t : Ine (F := E) A, Valued.v ((a (ineIncl hu (ι t)) : (u.adicCompletion L)ˣ) : u.adicCompletion L) = 1 :=
    fun t => DiscreteGroups.sglob.DzType.val_artin_ine ha (ι t)
  let π : Ine (F := E) A →* Multiplicative K :=
    MonoidHom.mk' (fun t => Multiplicative.ofAdd (abelian₂ (a (ineIncl hu (ι t))))) fun t t' => by
      rw [map_mul, map_mul, map_mul, hadd _ _ (hval t) (hval t')]
      rfl
  have hπ : ∀ t, Multiplicative.toAdd (π t) = abelian₂ (a (ineIncl hu (ι t))) := fun _ => rfl
  refine ⟨K, inferInstance, inferInstance, f, π, hcard, hfo, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb1, hby⟩ := hLs (Multiplicative.toAdd y)
    obtain ⟨t₁, ht₁⟩ := DiscreteGroups.sglob.DzType.exists_ine_of_v_eq_one ha b hb1
    obtain ⟨t, rfl⟩ := hιs t₁
    refine ⟨t, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hπ, ht₁, hby]
  · have hcont : Continuous fun t : Ine (F := E) A => a (ineIncl hu (ι t)) :=
      ha.cont.comp (UpperTheory.continuous_inertia_restriction_of_compat A ι hι)
    have hball : IsOpen {b : (u.adicCompletion L)ˣ | ((b : u.adicCompletion L) - 1) * (ϖ ^ 2)⁻¹ ∈ (O : Set (u.adicCompletion L))} :=
      (Valued.isOpen_valuationSubring _).preimage
        (((Units.continuous_val).sub continuous_const).mul continuous_const)
    have hU := hball.preimage hcont
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) ?_)
    · simp [O]
    · intro t ht
      apply Multiplicative.toAdd.injective
      refine hL0 _ ?_
      have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
      have h1 : Valued.v ((((a (ineIncl hu (ι t)) : (u.adicCompletion L)ˣ) : u.adicCompletion L) - 1) * (ϖ ^ 2)⁻¹) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff _ _).1 ht
      rw [map_mul, map_inv₀, map_pow, mul_inv_le_iff₀ (pow_pos (zero_lt_iff.2 hv0) 2), one_mul] at h1
      refine lt_of_le_of_lt h1 ?_
      rw [pow_two]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 hv0) hϖ1
  · intro t t' htt
    have hW : WeilRel (frob h : G E Ω).toRingEquiv (ineIncl hu (ι t)) (ineIncl hu (ι t')) := by
      intro z
      have e : (t' : G E Ω) = (frob h : G E Ω) * t * (frob h : G E Ω)⁻¹ := congrArg Subtype.val htt
      show (frob h : G E Ω) ((t : G E Ω) z) = (t' : G E Ω) ((frob h : G E Ω) z)
      rw [e]
      simp [AlgEquiv.mul_apply]
    have hP : PlaceIso A u A u (frob h : G E Ω).toRingEquiv (s.toRingEquiv : L →+* L) i :=
      ⟨fun z => apply_mem_iff_of_mem_Dec hφ.1 z, hs, hic, hil⟩
    have e := isLocalArtin_transport GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits' L Ω A u hu L Ω A u hu
      _ _ i hP a a ha ha _ _ hW
    have hiϖ : i ϖ = ϖ := by
      rw [hϖdef, hil]
      congr 1
      exact s.commutes (c : E)
    apply Multiplicative.toAdd.injective
    rw [hπ, e, toAdd_ofAdd, hπ]
    exact hLi i f hiϖ hiv hρi _ (hval t)

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.junkEx :
    UpperTheory.Zero.LLC.JunkEx := by
  intro E Ω _ _ _ _ _ A w h n hn
  obtain ⟨K, _, _, f, π, hc, ho, hs, hop, he⟩ := UpperTheory.Zero.LLC.junkData E Ω A w h n hn
  obtain ⟨J, h1, h2, h3, h4⟩ := UpperTheory.tameInertiaCharacter_frobenius_conj_eq_pow h n hn K f π hc ho hs hop he
  exact ⟨J, h1, h2, h3, fun _ V ξ hξ hV => h4 V ξ hξ hV⟩

end
