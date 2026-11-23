import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PointIdealComapPrimeLiftStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ResidueModelAtPrimeStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mem_minimalPrimes_map_iff_comap {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R']
    [Algebra R R'] (Mo : Submonoid R) [IsLocalization Mo R'] (J : Ideal (MRing ι R)) (W' : Ideal (MRing ι R')) :
    W' ∈ (J.map (MvPolynomial.map (algebraMap R R') : MRing ι R →+* MRing ι R')).minimalPrimes ↔
      W'.comap (MvPolynomial.map (algebraMap R R') : MRing ι R →+* MRing ι R') ∈ J.minimalPrimes := by
  letI := MvPolynomial.algebraMvPolynomial (σ := (Σ k, ι k)) (R := R) (S := R')
  haveI : IsLocalization (Mo.map (C (σ := (Σ k, ι k)) (R := R))) (MRing ι R') :=
    MvPolynomial.isLocalization Mo R'
  have h := IsLocalization.minimalPrimes_map (Mo.map (C (σ := (Σ k, ι k)) (R := R))) (MRing ι R') J
  have e : algebraMap (MRing ι R) (MRing ι R') = MvPolynomial.map (algebraMap R R') := rfl
  rw [e] at h
  rw [h]
  rfl

theorem mem_fibre_minimalPrimes_iff {K : Type} {ι : K → Type} {A O : Type} [CommRing A] [CommRing O]
    [IsLocalRing O] [Algebra A O] (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m]
    (Pa : Ideal (MRing ι A)) (W' : Ideal (MRing ι O)) :
    W' ∈ (Pa.map (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O) ⊔
        (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O)).minimalPrimes ↔
      W'.comap (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O) ∈
        (Pa ⊔ m.map (C : A →+* MRing ι A)).minimalPrimes := by
  have e : Pa.map (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O) ⊔
      (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) =
      (Pa ⊔ m.map (C : A →+* MRing ι A)).map
        (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O) := by
    rw [Ideal.map_sup, Ideal.map_map, ← IsLocalization.AtPrime.map_eq_maximalIdeal m O, Ideal.map_map,
      MvPolynomial.map_comp_C]
  rw [e]
  exact mem_minimalPrimes_map_iff_comap m.primeCompl _ W'

theorem mem_minimalPrimes_of_unique_contraction {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T)
    {J₀ W₀ : Ideal S} {Pa Ja Wa : Ideal T} (hW₀ : W₀ ∈ J₀.minimalPrimes) (hWa : Wa.IsPrime) (hJa : Ja ≤ Wa)
    (hc : Wa.comap ψ = W₀) (hJ : J₀ ≤ Ja.comap ψ) (hP : Pa ≤ Ja)
    (hu : ∀ Q : Ideal T, Q.IsPrime → Pa ≤ Q → Q.comap ψ = W₀ → Q = Wa) : Wa ∈ Ja.minimalPrimes := by
  refine ⟨⟨hWa, hJa⟩, fun Q hQ hQW => ?_⟩
  haveI := hQ.1
  have h1 : Q.comap ψ ≤ W₀ := hc ▸ Ideal.comap_mono hQW
  have h2 : W₀ ≤ Q.comap ψ :=
    hW₀.2 ⟨Ideal.comap_isPrime _ _, hJ.trans (Ideal.comap_mono hQ.2)⟩ h1
  exact (hu Q hQ.1 (hP.trans hQ.2) (le_antisymm h1 h2)).ge

theorem isMultiHomogIdeal_map_C {K : Type} [DecidableEq K] {ι : K → Type} {R : Type} [CommRing R] (I : Ideal R) :
    IsMultiHomogIdeal (I.map (C : R →+* MRing ι R)) := by
  classical
  intro f hf b
  rw [MvPolynomial.mem_map_C_iff] at hf ⊢
  intro d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hf d
  · exact I.zero_mem

theorem intCast_injective_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    Function.Injective (Int.castRingHom Ω) := by
  obtain ⟨-, -, hH, -⟩ := h
  refine (injective_iff_map_eq_zero _).2 fun n hn => ?_
  have hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have : (n : Ω) = 0 := by simpa using hn
    have e : ((n : MvPolynomial K Ω)) = C (n : Ω) := (map_intCast (C : Ω →+* MvPolynomial K Ω) n).symm
    simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, e, this]
  have h0 : (mCoordIdeal y).comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ := hH
  rw [h0] at hmem
  exact (Submodule.mem_bot _).1 hmem

theorem exists_algebra_of_injective (A Ω : Type) [CommRing A] [Field Ω] [Algebra A Ω]
    (hinj : Function.Injective (algebraMap A Ω)) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] : ∃ _ : Algebra O Ω, IsScalarTower A O Ω := by
  have hu : ∀ s : m.primeCompl, IsUnit (algebraMap A Ω s) := by
    intro s
    refine IsUnit.mk0 _ ?_
    intro h0
    have h1 : (s : A) = 0 := hinj (by rw [h0, map_zero])
    exact s.2 (h1 ▸ m.zero_mem)
  refine ⟨(IsLocalization.lift hu (S := O)).toAlgebra, ?_⟩
  letI : Algebra O Ω := (IsLocalization.lift hu (S := O)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq hu a).symm

def coneWt (K : Type) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem pointConeMap_monomial_isWeightedHomogeneous {K : Type} [DecidableEq K] {ι : K → Type} {O : Type}
    [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ] (z : (Σ k, ι k) → Φ) (d : (Σ k, ι k) →₀ ℕ) (a : O) :
    IsWeightedHomogeneous (coneWt K) (pointConeMap O z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := Φ) (coneWt K) p.1).C_mul (z p)).pow (d p)

theorem pointConeMap_component {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] {Φ : Type}
    [Field Φ] [Algebra O Φ] (z : (Σ k, ι k) → Φ) (b : K → ℕ) (f : MRing ι O) :
    weightedHomogeneousComponent (coneWt K) b (pointConeMap O z f) =
      pointConeMap O z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := pointConeMap_monomial_isWeightedHomogeneous (K := K) (O := O) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι O)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]

theorem isMultiHomogIdeal_pointIdeal_sup_map_C {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O]
    {Φ : Type} [Field Φ] [Algebra O Φ] (z : (Σ k, ι k) → Φ) (I : Ideal O) :
    IsMultiHomogIdeal (pointIdeal O z ⊔ I.map (C : O →+* MRing ι O)) := by
  intro f hf b
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  refine Submodule.add_mem_sup ?_ (isMultiHomogIdeal_map_C I v hv b)
  rw [pointIdeal, RingHom.mem_ker] at hu ⊢
  have h := pointConeMap_component (O := O) z b u
  rw [show (pointConeMap O z) u = 0 from hu, map_zero] at h
  exact h.symm

theorem isPrime_map_and_comap_map {K : Type} {ι : K → Type} {A O : Type} [CommRing A] [CommRing O]
    [Algebra A O] (Mo : Submonoid A) [IsLocalization Mo O] {Wa : Ideal (MRing ι A)} (hWa : Wa.IsPrime)
    (hd : ∀ s ∈ Mo, (C s : MRing ι A) ∉ Wa) :
    (Wa.map (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O)).IsPrime ∧
      (Wa.map (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O)).comap
        (MvPolynomial.map (algebraMap A O) : MRing ι A →+* MRing ι O) = Wa := by
  letI := MvPolynomial.algebraMvPolynomial (σ := (Σ k, ι k)) (R := A) (S := O)
  haveI : IsLocalization (Mo.map (C (σ := (Σ k, ι k)) (R := A))) (MRing ι O) :=
    MvPolynomial.isLocalization Mo O
  have hdisj : Disjoint ((Mo.map (C (σ := (Σ k, ι k)) (R := A)) : Submonoid (MRing ι A)) : Set (MRing ι A))
      (Wa : Set (MRing ι A)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hd s hs hmem
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Mo.map (C (σ := (Σ k, ι k)) (R := A))) _ Wa hWa hdisj,
    IsLocalization.under_map_of_isPrime_disjoint (Mo.map (C (σ := (Σ k, ι k)) (R := A))) (MRing ι O) hWa hdisj⟩

theorem exists_card_quotient_eq_pow {A : Type} [CommRing A] [Module.Finite ℤ A] (p : ℕ) [Fact p.Prime]
    (m : Ideal A) [m.IsMaximal] (hpm : (p : A) ∈ m) : ∃ fd : ℕ, Nat.card (A ⧸ m) = p ^ fd := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have hp0 : ((p : ℕ) : A ⧸ m) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hpm
    simpa using h
  haveI hchar : CharP (A ⧸ m) p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (ringChar.dvd hp0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h ▸ ringChar.charP _
  letI : Algebra (ZMod p) (A ⧸ m) := ZMod.algebra _ p
  haveI : Module.Finite ℤ (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (ZMod p) (A ⧸ m) := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) (A ⧸ m)
  haveI : Finite (A ⧸ m) := Module.finite_of_finite (ZMod p)
  refine ⟨Module.finrank (ZMod p) (A ⧸ m), ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem intNumL_of_isFibreComp {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {A : Type} [CommRing A] [Algebra A Ω] [IsDedekindDomain A]
    [Module.Finite ℤ A] (hconst : HasConstants ℤ A y) (p : ℕ) [Fact p.Prime] (m : Ideal A) [m.IsPrime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
    [Algebra O Ω] [IsScalarTower A O Ω] (hpm : (p : A) ∈ m) (fd : ℕ) (hcard : Nat.card (A ⧸ m) = p ^ fd)
    {W' : Ideal (MRing ι O)} (hW : IsFibreComp (pointIdeal O y) W') (l : List (K → ℤ)) :
    intNumL (ZMod p) (extTo (ZMod p) (W'.comap (MvPolynomial.map (Int.castRingHom O)))) l =
      (fd : ℤ) * vNumL W' l := by
  have hJ : IsMultiHomogIdeal (pointIdeal O y ⊔ (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O)) :=
    isMultiHomogIdeal_pointIdeal_sup_map_C y _
  have hWh : IsMultiHomogIdeal W' := MinimalPrimeMultiHomog.proof.{0} O K ι _ W' hJ hW.1
  exact GlobalTheory.T.residue_model_at_prime K ι Ω y A hconst p m O hpm fd hcard W' hW.1.1.1 hWh (le_sup_left.trans hW.1.1.2)
    (le_sup_right.trans hW.1.1.2) l

theorem classNum_eq_zero_of_vNumL_eq {K : Type} [DecidableEq K] {ι : K → Type} {O O' : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    {W : Ideal (MRing ι O)} {W' : Ideal (MRing ι O')} (c : ℤ) (h : ∀ l, vNumL W l = c * vNumL W' l)
    {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (h0 : classNum cls H Q W' = 0) :
    classNum cls H Q W = 0 := by
  have e : classNum cls H Q W = c * classNum cls H Q W' := by
    unfold classNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [h]
    ring
  rw [e, h0, mul_zero]

theorem powerSumsVanish_extTo_of_atPlacesOver : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (N : ℕ) (x : Fin N → K → ℤ), (AtPlacesOver A Ω p fun O _ _ _ _ => PowerSumsVanish (pointIdeal O y) D x) → PowerSumsVanish (extTo (ZP p) (mCoordIdeal y)) D x := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hinj hconst D harith p N x hpl
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hint := intCast_injective_of_isArithVar harith
  have hinjZ : Function.Injective (algebraMap ℤ Ω) := by
    have h : algebraMap ℤ Ω = Int.castRingHom Ω := RingHom.ext_int _ _
    rwa [h]
  have hconstZ : HasConstants ℤ ℤ y := fun c _ a => Subalgebra.algebraMap_mem _ a
  obtain ⟨algZ, towZ⟩ := exists_algebra_of_injective ℤ Ω hinjZ (Ideal.span {((p : ℕ) : ℤ)}) (ZP p)
  have hcastZ : algebraMap ℤ (ZP p) = Int.castRingHom (ZP p) := RingHom.ext_int _ _
  have hP0 : pointIdeal ℤ y = mCoordIdeal y := by
    have h := (GlobalTheory.T.point_ideal_comap_prime_lift K ι Ω y ℤ (fun c _ a => Subalgebra.algebraMap_mem _ a)).1
    have e : (MvPolynomial.map (Int.castRingHom ℤ) : MRing ι ℤ →+* MRing ι ℤ) = RingHom.id _ := by
      rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _]
      exact RingHom.ext fun f => MvPolynomial.map_id f
    rw [e, Ideal.comap_id] at h
    exact h
  have hZ' := (GlobalTheory.T.localization_model_over_place K ι Ω y ℤ hinjZ hconstZ D harith (Ideal.span {((p : ℕ) : ℤ)}) (ZP p)).1
  rw [hP0] at hZ'
  have hZ : extTo (ZP p) (mCoordIdeal y) = pointIdeal (ZP p) y := by
    rw [hZ', hcastZ]
    rfl
  rw [hZ]
  intro W hW k hk Q hQ
  have hWmin := hW.1
  rw [hZ'] at hWmin
  have hW0min := (mem_fibre_minimalPrimes_iff (Ideal.span {((p : ℕ) : ℤ)}) _ W).1 hWmin
  rw [hcastZ] at hW0min
  obtain ⟨W₀, hW₀⟩ : ∃ W₀, W₀ = W.comap (MvPolynomial.map (Int.castRingHom (ZP p)) : MRing ι ℤ →+* MRing ι (ZP p)) := ⟨_, rfl⟩
  rw [← hW₀] at hW0min
  have hW0p : W₀.IsPrime := hW0min.1.1
  have hW0rel : IsRelevant W₀ := by
    intro k
    obtain ⟨i, hi⟩ := hW.2 k
    refine ⟨i, fun h => hi ?_⟩
    rw [hW₀, Ideal.mem_comap, map_X] at h
    exact h
  have hle : mCoordIdeal y ≤ W₀ := le_sup_left.trans hW0min.1.2
  obtain ⟨hcomp, hex, -⟩ := GlobalTheory.T.point_ideal_comap_prime_lift K ι Ω y A hconst
  obtain ⟨Wa, ⟨hWap, hWapt, hWac⟩, hu⟩ := hex W₀ hW0p hW0rel hle
  obtain ⟨m, hm⟩ : ∃ m, m = Wa.comap (C : A →+* MRing ι A) := ⟨_, rfl⟩
  haveI hmp : m.IsPrime := hm ▸ Ideal.comap_isPrime _ _
  have hCp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W₀ :=
    (le_sup_right.trans hW0min.1.2) (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  have hmapC : ∀ n : ℤ, (MvPolynomial.map (Int.castRingHom A) (C n : MRing ι ℤ)) = C (n : A) := by
    intro n
    rw [map_C]
    rfl
  have hpm : ((p : ℕ) : A) ∈ m := by
    rw [← hWac, Ideal.mem_comap, hmapC] at hCp
    rw [hm, Ideal.mem_comap]
    simpa using hCp
  have hp0 : ((p : ℕ) : A) ≠ 0 := by
    intro h0
    have h1 : algebraMap A Ω ((p : ℕ) : A) = 0 := by rw [h0, map_zero]
    rw [map_natCast] at h1
    have h2 : Int.castRingHom Ω ((p : ℕ) : ℤ) = 0 := by simpa using h1
    have h3 : ((p : ℕ) : ℤ) = 0 := hint (by rw [h2, map_zero])
    exact p.2.ne_zero (by exact_mod_cast h3)
  have hmne : m ≠ ⊥ := fun h => hp0 ((Submodule.mem_bot _).1 (h ▸ hpm))
  haveI hmax : m.IsMaximal := Ideal.IsPrime.isMaximal hmp hmne
  obtain ⟨fd, hfd⟩ := exists_card_quotient_eq_pow (p : ℕ) m hpm
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hmne (Localization.AtPrime m)
  obtain ⟨algO, towO⟩ := exists_algebra_of_injective A Ω hinj m (Localization.AtPrime m)
  have hO := (GlobalTheory.T.localization_model_over_place K ι Ω y A hinj hconst D harith m (Localization.AtPrime m)).1
  have hWaMin : Wa ∈ (pointIdeal A y ⊔ m.map (C : A →+* MRing ι A)).minimalPrimes := by
    refine mem_minimalPrimes_of_unique_contraction
      (MvPolynomial.map (Int.castRingHom A) : MRing ι ℤ →+* MRing ι A) hW0min hWap
      (sup_le hWapt (Ideal.map_le_iff_le_comap.2 hm.le)) hWac ?_ le_sup_left
      (fun Q hQ hPQ hc => hu Q ⟨hQ, hPQ, hc⟩)
    refine sup_le (hcomp.ge.trans (Ideal.comap_mono le_sup_left)) (Ideal.map_le_iff_le_comap.2 ?_)
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, Ideal.mem_comap, hmapC]
    refine Ideal.mem_sup_right ?_
    have h := Ideal.mem_map_of_mem (C : A →+* MRing ι A) hpm
    simpa using h
  obtain ⟨hW'p, hW'c⟩ := isPrime_map_and_comap_map (O := Localization.AtPrime m) m.primeCompl hWap
    (fun s hs h => hs (show s ∈ m by rw [hm, Ideal.mem_comap]; exact h))
  obtain ⟨W', hW'⟩ : ∃ W', W' = Wa.map (MvPolynomial.map (algebraMap A (Localization.AtPrime m)) :
      MRing ι A →+* MRing ι (Localization.AtPrime m)) := ⟨_, rfl⟩
  rw [← hW'] at hW'p hW'c
  have hcomp' : (MvPolynomial.map (Int.castRingHom (Localization.AtPrime m)) :
      MRing ι ℤ →+* MRing ι (Localization.AtPrime m)) =
      (MvPolynomial.map (algebraMap A (Localization.AtPrime m))).comp
        (MvPolynomial.map (Int.castRingHom A)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_) <;> simp
  have hc0 : W'.comap (MvPolynomial.map (Int.castRingHom (Localization.AtPrime m))) = W₀ := by
    rw [hcomp', ← Ideal.comap_comap, hW'c, hWac]
  have hfib : IsFibreComp (pointIdeal (Localization.AtPrime m) y) W' := by
    refine ⟨?_, fun k => ?_⟩
    · rw [hO]
      refine (mem_fibre_minimalPrimes_iff m _ W').2 ?_
      rw [hW'c]
      exact hWaMin
    · obtain ⟨i, hi⟩ := hW0rel k
      refine ⟨i, fun h => hi ?_⟩
      rw [← hc0, Ideal.mem_comap, map_X]
      exact h
  have hv : PowerSumsVanish (pointIdeal (Localization.AtPrime m) y) D x :=
    hpl m hpm (Localization.AtPrime m)
  have hA := intNumL_of_isFibreComp y hconst (p : ℕ) m (Localization.AtPrime m) hpm fd hfd hfib
  have hcardZ : Nat.card (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) = (p : ℕ) ^ 1 := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (p : ℕ)).toEquiv, Nat.card_zmod, pow_one]
  have hB := intNumL_of_isFibreComp y hconstZ (p : ℕ) (Ideal.span {((p : ℕ) : ℤ)}) (ZP p)
    (by simpa using Ideal.mem_span_singleton_self (((p : ℕ) : ℤ))) 1 hcardZ hW
  refine classNum_eq_zero_of_vNumL_eq (fd : ℤ) (fun l => ?_) x _ Q (hv W' hfib k hk Q hQ)
  have h1 := hB l
  have h2 := hA l
  rw [← hW₀] at h1
  rw [hc0] at h2
  rw [← h2, h1]
  simp

end GlobalTheory.CompanionTheory.Ar.Num
