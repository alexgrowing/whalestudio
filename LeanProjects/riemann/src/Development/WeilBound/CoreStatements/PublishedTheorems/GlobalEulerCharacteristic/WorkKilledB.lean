import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.ExistsPrimeToPart
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ApplySubrepresentationCongr
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Shapiro
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.PoitouTate.NonemptyOfNatCastMemOfNeOne
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.ShapiroDefs
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroReal

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_b

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 1000000 in

theorem ratio_shortExact_prime (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hℓ : ∃ r : ℕ, ∀ m : T.X₂, (ℓ ^ r) • m = 0) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  haveI : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite S
  have hp : ℓ.Prime := Fact.out
  haveI : Nonempty S := nonempty_of_natCast_mem_of_ne_one (N := ℓ) S hp.one_lt.ne' hSℓ
  obtain ⟨r, hr⟩ := hℓ
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have hsurj : Function.Surjective T.g.hom := (Rep.epi_iff_surjective _).1 hT.epi_g
  haveI : Finite T.X₁ := Finite.of_injective _ hinj
  haveI : Finite T.X₃ := Finite.of_surjective _ hsurj
  haveI : NeZero (ℓ ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K.1), (((ℓ ^ r : ℕ)) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSℓ v
    rw [Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem r hv
  let ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) := fun v =>
    (nonempty_algHom_of_isSepClosed : Nonempty (AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).some
  have h1 : ∀ m : T.X₁, (ℓ ^ r) • m = 0 := fun m => hinj (by
    rw [map_nsmul, hr, map_zero])
  have hA := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₁) (hM := h1)
    (r := 3) le_rfl
  have hB := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₂) (hM := hr)
    (r := 3) le_rfl
  have hpg : IsPGroup ℓ (Multiplicative T.X₂) := fun g => ⟨r, by
    show Multiplicative.toAdd (g ^ (ℓ ^ r)) = Multiplicative.toAdd 1
    rw [toAdd_pow]; exact hr _⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn2 : Nat.card T.X₂ = ℓ ^ n := by rw [← hn]; rfl
  have hn' : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₂ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSℓ v
    rw [hn2, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem n hv
  exact gsEulerRatio_shortExact_of_bijective S ιr hT hn' hA hB

theorem ratio_shortExact_prime_card (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hc : ∃ n : ℕ, Nat.card T.X₂ = ℓ ^ n) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  obtain ⟨n, hn⟩ := hc
  exact ratio_shortExact_prime ℓ K S hS hSℓ ιr T hT ⟨n, fun m => by rw [← hn]; exact card_nsmul_eq_zero'⟩

theorem ratio_eq_one_of_cyclic_pow (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    [IsCyclic (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))]
    {a : ℕ} (hcard : Nat.card (galUnramifiedOutside K.1 ℚ̄ S ⧸
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0)
    (hL1 : ∀ ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S) (W_killed_a.resTo S L hL M) ιrL = 1) :
    gsEulerRatio S M ιr = 1 := by
  classical
  have : Finite S := hS
  have hp : ℓ.Prime := Fact.out
  let P : ℕ → Prop := fun n => ∃ k, n = ℓ ^ k
  have hPdvd : ∀ m n, m ∣ n → P n → P m := by
    rintro m n hmn ⟨k, rfl⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hmn
    exact ⟨j, rfl⟩
  have hPmul : ∀ m n, P m → P n → P (m * n) := by
    rintro m n ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (pow_add ℓ i j).symm⟩
  have hχ : IsMultiplicativeOn P
      (fun (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep A] =>
        gsEulerRatio S A ιr) :=
    { iso := fun {A B} _ _ _ _ e => gsEulerRatio_eq_of_iso S A ιr e
      shortExact := fun {T} _ _ _ _ hT hP => by
        obtain ⟨k, hk⟩ := hP
        exact ratio_shortExact_prime ℓ K S hS hSℓ ιr T hT ⟨k, fun m => by
          rw [← hk]; exact card_nsmul_eq_zero'⟩ }
  have hcardM : P (Nat.card M) := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hℓ x)
    rw [hx] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hp).1 this
  have hpow := hχ.coind_res_eq_pow hPdvd hPmul (gsOpenSubgroup S hL) hcard M hcardM hℓ
  obtain ⟨ιrL, hsh⟩ := exists_gsEulerRatio_coind_eq S hL ιr
  have hfin : Finite (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) :=
    inferInstanceAs (Finite M)
  have hsh1 := hsh (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)
  have he : gsEulerRatio S M ιr ^ (ℓ ^ a) = 1 := hpow.symm.trans (hsh1.trans (hL1 ιrL))
  have hpos : 0 < gsEulerRatio S M ιr := by
    obtain ⟨k, hk⟩ := hcardM
    refine gsEulerRatio_pos S M ιr fun v hv => hSℓ v ?_
    rw [hk, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem k hv
  exact (pow_eq_one_iff_of_nonneg hpos.le (pow_ne_zero _ hp.ne_zero)).1 he

noncomputable def coindStagesEquiv {k G : Type} [CommRing k] [Group G] (U W : Subgroup G) (hUW : U ≤ W)
    (A : Rep.{0} k G) :
    (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A)))).ρ.Equiv
      (Rep.coind U.subtype (Rep.res U.subtype A)).ρ where
  toFun F := ⟨fun g => (F.1 g).1 1, by
    intro u g
    have h3 : (F.1 (u.1 * g)).1 1 = (F.1 g).1 (1 * ⟨u.1, hUW u.2⟩) :=
      congrArg (fun x => x.1 (1 : W)) (F.2 ⟨u.1, hUW u.2⟩ g)
    have h2 := (F.1 g).2 ⟨⟨u.1, hUW u.2⟩, by simp [Subgroup.mem_subgroupOf]⟩ 1
    rw [one_mul] at h3
    rw [mul_one] at h2
    exact h3.trans h2⟩
  map_add' F F' := Subtype.ext (funext fun g => rfl)
  map_smul' c F := Subtype.ext (funext fun g => rfl)
  invFun f := ⟨fun g => ⟨fun w => f.1 (w.1 * g), by
      intro u' w
      have := f.2 ⟨u'.1.1, u'.2⟩ (w.1 * g)
      simpa [mul_assoc] using this⟩, by
    intro w g
    apply Subtype.ext
    funext x
    change f.1 (x.1 * (w.1 * g)) = f.1 ((x * w).1 * g)
    rw [Subgroup.coe_mul, mul_assoc]⟩
  left_inv F := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext w
    have h := congrArg (fun x => x.1 (1 : W)) (F.2 w g)
    change (F.1 (w.1 * g)).1 1 = (F.1 g).1 (1 * w) at h
    rw [one_mul] at h
    exact h
  right_inv f := by
    apply Subtype.ext
    funext g
    change f.1 ((1 : W).1 * g) = f.1 g
    rw [OneMemClass.coe_one, one_mul]
  isIntertwining' h := LinearMap.ext fun F => Subtype.ext (funext fun g => rfl)

theorem coind_stages {k G : Type} [CommRing k] [Group G] (U W : Subgroup G) (hUW : U ≤ W) (A : Rep.{0} k G) :
    Nonempty (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A))) ≅
      Rep.coind U.subtype (Rep.res U.subtype A)) :=
  ⟨Rep.mkIso (coindStagesEquiv U W hUW A)⟩

set_option maxHeartbeats 1000000 in

theorem isMultiplicativeOn_ratio_coind (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    IsMultiplicativeOn (fun n => ∃ k, n = ℓ ^ k)
      (fun (X : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep X] =>
        gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype X) ιr) := by
  have hp : ℓ.Prime := Fact.out
  exact
  { iso := fun {A B} _ _ _ _ e =>
      gsEulerRatio_eq_of_iso S _ ιr ((Rep.coindFunctor (ULift.{0} ℤ) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype).mapIso e)
    shortExact := fun {T} _ _ _ _ hT hP => by
      have hT' := shortExact_coindShortComplexOf (G := (galUnramifiedOutside K.1 ℚ̄ S)) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) hT
      obtain ⟨k, hk⟩ := hP
      have hcc := card_coind_gsOpenSubgroup S hL' T.X₂
      have hfin : Finite (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype T.X₂) :=
        Nat.finite_of_card_ne_zero (by rw [hcc, hk]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
      have i1 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₁ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₁
      have i2 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₂
      have i3 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₃ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₃
      have hfin2 : Finite (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ := hfin
      have hcc2 : Nat.card (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ = ℓ ^ (k * Module.finrank K.1 L'.1) := by
        rw [pow_mul, ← hk]; exact hcc
      have key := ratio_shortExact_prime_card ℓ K S hS hSℓ ιr (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T) hT' ⟨_, hcc2⟩
      exact key }

theorem ratio_coind_stage_pow (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (K'' : FiniteSubfield) [Fact (K ≤ K'')] (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    [((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal]
    [IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))]
    {a : ℕ} (hcard : Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] (hℓ : ∀ m : M, ℓ • m = 0) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr ^ (ℓ ^ a) := by
  classical
  have hp : ℓ.Prime := Fact.out
  let W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S) := gsOpenSubgroup S hL'
  haveI : CompactSpace (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := compactSpace_openSubgroup (gsOpenSubgroup S hL')
  let H : OpenSubgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :=
    ⟨(gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), (gsOpenSubgroup S hK'').isOpen.preimage continuous_subtype_val⟩
  haveI : (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal := inferInstanceAs ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal
  haveI : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :=
    inferInstanceAs (IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))))
  have hχ := isMultiplicativeOn_ratio_coind ℓ K S hS hSℓ ιr L' hL'
  have hPdvd : ∀ m n, m ∣ n → (∃ k, n = ℓ ^ k) → (∃ k, m = ℓ ^ k) := by
    rintro m n hmn ⟨k, rfl⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hmn
    exact ⟨j, rfl⟩
  have hPmul : ∀ m n, (∃ k, m = ℓ ^ k) → (∃ k, n = ℓ ^ k) → (∃ k, m * n = ℓ ^ k) := by
    rintro m n ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (pow_add ℓ i j).symm⟩
  have hcM : ∃ k, Nat.card M = ℓ ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hℓ x)
    rw [hx] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hp).1 this
  have : Finite (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := inferInstanceAs (Finite M)
  have hpow := hχ.coind_res_eq_pow hPdvd hPmul H (p := ℓ) hcard (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) hcM
    (fun m => hℓ m)
  obtain ⟨e⟩ := coind_stages (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) hle M
  have e' : Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M))) ≅
      Rep.coind (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := e
  have hd1 : IsDiscreteRep (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M))) := isDiscreteRep_coind H _
  have hd2 : IsDiscreteRep (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)))) :=
    isDiscreteRep_coind (gsOpenSubgroup S hL') _
  rw [← hpow]
  exact (gsEulerRatio_eq_of_iso S _ ιr e').symm

theorem exists_prime_to_part (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (L : FiniteSubfield) [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    ∃ (K'' : FiniteSubfield) (_ : Fact (K ≤ K''))
      (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧
      IsCyclic ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ∧
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ ∧
      ∃ hnorm : ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal,
      (haveI := hnorm; IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) ∧
      ∃ a : ℕ, Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a :=
  GlobalEulerCharacteristicAlt.exists_prime_to_part ℓ K S L hL L' hL' hle hcyc

theorem exists_ratio_coind_eq_resTo (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (K' : FiniteSubfield) [Fact (K ≤ K')] (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] :
    ∃ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
        gsEulerRatio (placesOver S) (W_killed_a.resTo S K' hK' M) ιr' := by
  obtain ⟨ιr', hsh⟩ := exists_gsEulerRatio_coind_eq S hK' ιr
  have : Finite (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := inferInstanceAs (Finite M)
  exact ⟨ιr', hsh _⟩

theorem ratio_coind_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (W_killed_a.resTo S K' hK' M) ιr' = 1)
    (L' : FiniteSubfield) [Fact (K ≤ L')]
    (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr = 1 := by

  classical
  have hp : ℓ.Prime := Fact.out
  haveI := hN
  have : Finite S := hS
  obtain ⟨K'', hKK'', hK'', hUle, hle'', hcyc'', hcop, hnorm, hcycW, a, hcard⟩ :=
    exists_prime_to_part ℓ K S L hL L' hL' hle hcyc
  haveI := hKK''
  haveI := hnorm
  haveI := hcycW
  obtain ⟨ιr'', h3⟩ := exists_ratio_coind_eq_resTo K S ιr K'' hK'' M
  have h1 : gsEulerRatio (placesOver S) (W_killed_a.resTo S K'' hK'' M) ιr'' = 1 :=
    hK K'' hK'' hUle hcyc'' hcop ιr''
  have h2 := ratio_coind_stage_pow ℓ K S hS hSℓ ιr L' hL' K'' hK'' hle'' hcard M hℓ
  have he : gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr ^ (ℓ ^ a) = 1 :=
    h2.symm.trans (h3.trans h1)
  have hcM : ∃ k, Nat.card M = ℓ ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hℓ x)
    rw [hx] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hp).1 this
  obtain ⟨k, hk⟩ := hcM
  have hcc := card_coind_gsOpenSubgroup S hL' (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)
  have hcc' : Nat.card (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) =
      ℓ ^ (k * Module.finrank K.1 L'.1) := by
    rw [hcc, pow_mul, ← hk]
  have : Finite (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcc']; exact pow_ne_zero _ hp.ne_zero)
  have hpos : 0 < gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr := by
    refine gsEulerRatio_pos S _ ιr fun v hv => hSℓ v ?_
    rw [hcc', Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem _ hv
  exact (pow_eq_one_iff_of_nonneg hpos.le (pow_ne_zero _ hp.ne_zero)).1 he

end PositivityTheory.Lit1.GEN.W_killed_b
