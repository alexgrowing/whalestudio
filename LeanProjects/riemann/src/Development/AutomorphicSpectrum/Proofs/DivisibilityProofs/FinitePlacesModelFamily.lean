import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivCycleMapLocalisation
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycleStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PointIdealComapPrimeLiftStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ResidueModelAtPrimeStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.Places

variable {K : Type} {ι : K → Type}

theorem map_map_cast {A O : Type} [CommRing A] [CommRing O] [Algebra A O] (f : MRing ι ℤ) :
    MvPolynomial.map (algebraMap A O) (MvPolynomial.map (Int.castRingHom A) f) =
      MvPolynomial.map (Int.castRingHom O) f := by
  have h : (algebraMap A O).comp (Int.castRingHom A) = Int.castRingHom O := RingHom.ext_int _ _
  rw [MvPolynomial.map_map, h]

theorem comap_cast_eq {A O : Type} [CommRing A] [CommRing O] [Algebra A O] (W : Ideal (MRing ι O)) :
    W.comap (MvPolynomial.map (Int.castRingHom O)) =
      (W.comap (MvPolynomial.map (algebraMap A O))).comap (MvPolynomial.map (Int.castRingHom A)) := by
  ext g
  simp only [Ideal.mem_comap, map_map_cast]

theorem comap_pointIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A O : Type} [CommRing A] [CommRing O]
    [Algebra A O] [Algebra A Ω] [Algebra O Ω] [IsScalarTower A O Ω] :
    (pointIdeal O y : Ideal (MRing ι O)).comap (MvPolynomial.map (algebraMap A O)) = pointIdeal A y := by
  ext g
  rw [Ideal.mem_comap, pointIdeal, pointIdeal, RingHom.mem_ker, RingHom.mem_ker]
  simp only [pointConeMap]
  rw [MvPolynomial.aeval_map_algebraMap]

theorem mem_of_divCycle_ne_zero {R : Type} [CommRing R] {P W : Ideal (MRing ι R)} {f : MRing ι R}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

theorem isRelevant_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {W : Ideal (MRing ι S)}
    (h : IsRelevant W) : IsRelevant (W.comap (MvPolynomial.map φ)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  exact ⟨i, by simpa [Ideal.mem_comap] using hi⟩

theorem isRelevant_of_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {W : Ideal (MRing ι S)}
    (h : IsRelevant (W.comap (MvPolynomial.map φ))) : IsRelevant W := by
  intro k
  obtain ⟨i, hi⟩ := h k
  exact ⟨i, by simpa [Ideal.mem_comap] using hi⟩

theorem isMultiHomog_map [DecidableEq K] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    {G : MRing ι R} {b : K → ℕ} (hG : IsMultiHomog G b) : IsMultiHomog (MvPolynomial.map φ G) b := by
  intro d hd
  apply hG
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

section Loc

variable {A O : Type} [CommRing A] [CommRing O] [Algebra A O] (m : Ideal A) [m.IsPrime]
  [IsLocalization.AtPrime O m]

attribute [local instance] MvPolynomial.algebraMvPolynomial

include m

theorem eq_of_comap_eq {W₁ W₂ : Ideal (MRing ι O)}
    (h : W₁.comap (MvPolynomial.map (algebraMap A O)) = W₂.comap (MvPolynomial.map (algebraMap A O))) :
    W₁ = W₂ := by
  haveI : IsLocalization (m.primeCompl.map (C (σ := (Σ k, ι k)) (R := A))) (MRing ι O) :=
    MvPolynomial.isLocalization m.primeCompl O
  have e : ∀ W : Ideal (MRing ι O), (W.comap (algebraMap (MRing ι A) (MRing ι O))).map
      (algebraMap (MRing ι A) (MRing ι O)) = W :=
    IsLocalization.map_comap (m.primeCompl.map (C (σ := (Σ k, ι k)) (R := A))) _
  have h' : W₁.comap (algebraMap (MRing ι A) (MRing ι O)) =
      W₂.comap (algebraMap (MRing ι A) (MRing ι O)) := h
  rw [← e W₁, ← e W₂, h']

theorem exists_prime_of_comap_C {W : Ideal (MRing ι A)} (hW : W.IsPrime)
    (hm : W.comap (C : A →+* MRing ι A) = m) :
    ∃ W' : Ideal (MRing ι O), W'.IsPrime ∧ W'.comap (MvPolynomial.map (algebraMap A O)) = W := by
  haveI : IsLocalization (m.primeCompl.map (C (σ := (Σ k, ι k)) (R := A))) (MRing ι O) :=
    MvPolynomial.isLocalization m.primeCompl O
  have hdisj : Disjoint ((m.primeCompl.map (C (σ := (Σ k, ι k)) (R := A)) : Submonoid (MRing ι A)) :
      Set (MRing ι A)) (W : Set (MRing ι A)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsW
    exact hs (by rw [← hm]; exact hsW)
  exact ⟨W.map (algebraMap (MRing ι A) (MRing ι O)),
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hW hdisj,
    IsLocalization.comap_map_of_isPrime_disjoint _ _ hW hdisj⟩

theorem comap_C_comap_eq [IsLocalRing O] {W : Ideal (MRing ι O)} (hW : W.IsPrime)
    (h : (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W) :
    (W.comap (MvPolynomial.map (algebraMap A O))).comap (C : A →+* MRing ι A) = m := by
  have h1 : W.comap (C : O →+* MRing ι O) = IsLocalRing.maximalIdeal O :=
    ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ W).ne_top
      (Ideal.map_le_iff_le_comap.mp h)).symm
  have h2 : (W.comap (MvPolynomial.map (algebraMap A O))).comap (C : A →+* MRing ι A) =
      (W.comap (C : O →+* MRing ι O)).comap (algebraMap A O) := by
    ext a
    simp [Ideal.mem_comap]
  rw [h2, h1]
  exact IsLocalization.AtPrime.comap_maximalIdeal O m

end Loc

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem maximal_le_of_C_mem {x : O} (hx : x ≠ 0) {W : Ideal (MRing ι O)} (hW : W.IsPrime)
    (hxW : (C x : MRing ι O) ∈ W) :
    (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O) ≤ W := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hp : (C ϖ : MRing ι O) ^ n ∈ W := by
    rw [← map_pow, ← hu, map_mul]
    exact W.mul_mem_right _ hxW
  have hϖW := hW.mem_of_pow_mem n hp
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨z, hz, rfl⟩
  rw [Set.mem_singleton_iff.mp hz]
  exact hϖW

theorem C_uniformiser_notMem {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) {ϖ : O} (hϖ : Irreducible ϖ)
    {W : Ideal (MRing ι O)} (hxW : (C x : MRing ι O) ∉ W) : (C ϖ : MRing ι O) ∉ W := by
  intro h
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  apply hxW
  rw [map_mul]
  exact W.mul_mem_left _ h

end DVR

end GlobalTheory.CompanionTheory.Ar.Num.Places

theorem GlobalTheory.CompanionTheory.Ar.Num.cycList_zp_eq_sum_places : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (Λ : Type) [Fintype Λ] (m : Λ → Ideal A) [∀ l, (m l).IsPrime], Function.Injective m → (∀ n : Ideal A, n.IsPrime → (((p : ℕ) : A) ∈ n ↔ n ∈ Set.range m)) → ∀ (O : Λ → Type) [∀ l, CommRing (O l)] [∀ l, IsDomain (O l)] [∀ l, IsDiscreteValuationRing (O l)] [∀ l, Algebra A (O l)] [∀ l, IsLocalization.AtPrime (O l) (m l)] [∀ l, Algebra (O l) Ω] [∀ l, IsScalarTower A (O l) Ω], ∀ fd : Λ → ℕ, (∀ l, Nat.card (A ⧸ m l) = (p : ℕ) ^ fd l) → ∀ (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ mCoordIdeal y → ∀ L : List (K → ℤ), L.length = D → cycList (divCycle (extTo (ZP p) (mCoordIdeal y)) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) L = ∑ l, (fd l : ℤ) * cycList (divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f)) L := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hinj hconst D hP p Λ _ m _ hminj hm O _ _ _ _ _ _ _ fd hfd a f hf hfP L hL
  classical
  haveI hpf : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨hcomapA, hlift, hdiv⟩ := GlobalTheory.T.point_ideal_comap_prime_lift K ι Ω y A hconst
  have hmod := fun l => GlobalTheory.T.localization_model_over_place K ι Ω y A hinj hconst D hP (m l) (O l)

  have hcomapO : ∀ l, (pointIdeal (O l) y : Ideal (MRing ι (O l))).comap
      (MvPolynomial.map (Int.castRingHom (O l))) = mCoordIdeal y := fun l => by
    rw [Places.comap_cast_eq (A := A), Places.comap_pointIdeal, hcomapA]
  have hfO : ∀ l, MvPolynomial.map (Int.castRingHom (O l)) f ∉ pointIdeal (O l) y := fun l h =>
    hfP (by rw [← hcomapO l]; exact h)
  have hpm : ∀ l, ((p : ℕ) : A) ∈ m l := fun l => (hm (m l) inferInstance).2 ⟨l, rfl⟩
  have hpmax : ∀ l, ((p : ℕ) : O l) ∈ IsLocalRing.maximalIdeal (O l) := fun l => by
    have e : (IsLocalRing.maximalIdeal (O l)).comap (algebraMap A (O l)) = m l :=
      IsLocalization.AtPrime.comap_maximalIdeal (O l) (m l)
    have h : ((p : ℕ) : A) ∈ (IsLocalRing.maximalIdeal (O l)).comap (algebraMap A (O l)) := by
      rw [e]
      exact hpm l
    simpa [Ideal.mem_comap] using h
  have hp0 : ∀ l, ((p : ℕ) : O l) ≠ 0 := fun l h0 => by
    have h1 : (C (((p : ℕ) : ℤ)) : MRing ι ℤ) ∈ mCoordIdeal y := by
      rw [← hcomapO l, Ideal.mem_comap, MvPolynomial.map_C]
      simp [h0]
    have h2 : ((p : ℕ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι ℤ) := h1
    rw [hP.2.2.1, Ideal.mem_bot] at h2
    exact p.2.ne_zero (by exact_mod_cast h2)

  have hfacts : ∀ l (W : Ideal (MRing ι (O l))),
      divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f) W ≠ 0 →
      W.IsPrime ∧ IsRelevant W ∧ pointIdeal (O l) y ≤ W ∧ IsMultiHomogIdeal W := fun l W h => by
    obtain ⟨hmin, hrel⟩ := Places.mem_of_divCycle_ne_zero h
    exact ⟨hmin.1.1, hrel, le_sup_left.trans hmin.1.2,
      MinimalPrimeMultiHomog.full (O l) K ι _ W
        (SupSpanMultiHomog.full (O l) K ι _ _ a (hmod l).2.1.multiProj.multiHomog
          (Places.isMultiHomog_map _ hf)) hmin⟩

  have hmult : ∀ l (W : Ideal (MRing ι (O l))), W.IsPrime → IsRelevant W → pointIdeal (O l) y ≤ W →
      divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f) W =
        divCycle (mCoordIdeal y) f (W.comap (MvPolynomial.map (Int.castRingHom (O l)))) := fun l W hW hrel hle => by
    have h1 := GlobalTheory.CompanionTheory.Ar.Num.divCycle_map_localisation K ι A (O l) (m l).primeCompl (pointIdeal A y)
      (MvPolynomial.map (Int.castRingHom A) f) W hW
    rw [Places.map_map_cast, ← (hmod l).1] at h1
    rw [h1, Places.comap_cast_eq (A := A)]
    refine hdiv f _ (Ideal.comap_isPrime _ W) (Places.isRelevant_comap _ hrel) ?_
    rw [← Places.comap_pointIdeal (O := O l)]
    exact Ideal.comap_mono hle
  have hCp : ∀ l (W : Ideal (MRing ι (O l))),
      (C (((p : ℕ) : ℤ)) : MRing ι ℤ) ∈ W.comap (MvPolynomial.map (Int.castRingHom (O l))) ↔
        (C ((p : ℕ) : O l) : MRing ι (O l)) ∈ W := fun l W => by
    rw [Ideal.mem_comap, MvPolynomial.map_C]
    simp
  have hfinZ := DivCycleFiniteSupport.full ℤ K ι (mCoordIdeal y) f
  have hfinl := fun l => DivCycleFiniteSupport.full (O l) K ι (pointIdeal (O l) y)
    (MvPolynomial.map (Int.castRingHom (O l)) f)
  let T : Finset (Ideal (MRing ι ℤ)) :=
    hfinZ.toFinset.filter fun W => (C (((p : ℕ) : ℤ)) : MRing ι ℤ) ∈ W
  let Tl : ∀ l, Finset (Ideal (MRing ι (O l))) := fun l =>
    (hfinl l).toFinset.filter fun W => (C ((p : ℕ) : O l) : MRing ι (O l)) ∈ W
  have hLeft : cycList (divCycle (extTo (ZP p) (mCoordIdeal y))
      (MvPolynomial.map (Int.castRingHom (ZP p)) f)) L =
      ∑ W ∈ T, divCycle (mCoordIdeal y) f W * intNumL (ZMod p) (extTo (ZMod p) W) L := by
    rw [← GlobalTheory.T.vertical_number_local_cycle K ι _ D hP p a f hf hfP L hL]
    unfold vertAt cycEval
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · refine Finset.sum_congr rfl fun W hW => ?_
      beta_reduce
      rw [if_pos (Finset.mem_filter.mp hW).2]
    · intro W hW
      rw [Function.mem_support] at hW
      have h1 := left_ne_zero_of_mul hW
      have h2 := right_ne_zero_of_mul hW
      by_cases hc : (C (((p : ℕ) : ℤ)) : MRing ι ℤ) ∈ W
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hfinZ.mem_toFinset.mpr h1, hc⟩)
      · beta_reduce at h2
        rw [if_neg hc] at h2
        exact absurd rfl h2
  have hRight : ∀ l, cycList (divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f)) L =
      ∑ W ∈ Tl l, divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f) W * vNumL W L := fun l => by
    unfold cycList cycEval
    rw [finsum_eq_sum_of_support_subset (s := Tl l)]
    intro W hW
    rw [Function.mem_support] at hW
    have h1 := left_ne_zero_of_mul hW
    have h2 := right_ne_zero_of_mul hW
    have hc : (C ((p : ℕ) : O l) : MRing ι (O l)) ∈ W := by
      by_contra hc
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (O l)
      exact h2 (GlobalTheory.T.vertical_number_zero_of_horizontal (O l) ϖ hϖ K ι _ D (hmod l).2.1 a _ (Places.isMultiHomog_map _ hf) (hfO l) W h1
        (Places.C_uniformiser_notMem (hpmax l) hϖ hc) L hL)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(hfinl l).mem_toFinset.mpr h1, hc⟩)
  have hsum : ∑ l, (fd l : ℤ) * cycList (divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f)) L =
      ∑ l, ∑ W ∈ Tl l, (fd l : ℤ) * (divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f) W * vNumL W L) :=
    Finset.sum_congr rfl fun l _ => by rw [hRight l, Finset.mul_sum]

  have hmem : ∀ l (W : Ideal (MRing ι (O l))), W ∈ Tl l →
      divCycle (pointIdeal (O l) y) (MvPolynomial.map (Int.castRingHom (O l)) f) W ≠ 0 ∧
      (C ((p : ℕ) : O l) : MRing ι (O l)) ∈ W := fun l W h => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    exact ⟨(hfinl l).mem_toFinset.mp h1, h2⟩
  rw [hLeft, hsum, Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => x.2.comap (MvPolynomial.map (Int.castRingHom (O x.1)))) ?_ ?_ ?_ ?_
  · rintro ⟨l, W⟩ hx
    obtain ⟨hne, hc⟩ := hmem l W (Finset.mem_sigma.mp hx).2
    obtain ⟨hWp, hrel, hle, -⟩ := hfacts l W hne
    refine Finset.mem_filter.mpr ⟨hfinZ.mem_toFinset.mpr ?_, (hCp l W).2 hc⟩
    rw [Function.mem_support, ← hmult l W hWp hrel hle]
    exact hne
  · rintro ⟨l₁, W₁⟩ hx₁ ⟨l₂, W₂⟩ hx₂ heq
    obtain ⟨hne₁, hc₁⟩ := hmem l₁ W₁ (Finset.mem_sigma.mp hx₁).2
    obtain ⟨hne₂, hc₂⟩ := hmem l₂ W₂ (Finset.mem_sigma.mp hx₂).2
    obtain ⟨hp₁, hrel₁, hle₁, -⟩ := hfacts l₁ W₁ hne₁
    obtain ⟨hp₂, hrel₂, hle₂, -⟩ := hfacts l₂ W₂ hne₂
    have heq' : W₁.comap (MvPolynomial.map (Int.castRingHom (O l₁))) =
        W₂.comap (MvPolynomial.map (Int.castRingHom (O l₂))) := heq
    have hA : ∀ l (W : Ideal (MRing ι (O l))), pointIdeal (O l) y ≤ W →
        pointIdeal A y ≤ W.comap (MvPolynomial.map (algebraMap A (O l))) := fun l W h => by
      rw [← Places.comap_pointIdeal (O := O l)]
      exact Ideal.comap_mono h
    have hlow : mCoordIdeal y ≤ W₁.comap (MvPolynomial.map (Int.castRingHom (O l₁))) := by
      rw [← hcomapO l₁]
      exact Ideal.comap_mono hle₁
    have hWA : W₁.comap (MvPolynomial.map (algebraMap A (O l₁))) =
        W₂.comap (MvPolynomial.map (algebraMap A (O l₂))) :=
      (hlift _ (Ideal.comap_isPrime _ W₁) (Places.isRelevant_comap _ hrel₁) hlow).unique
        ⟨Ideal.comap_isPrime _ W₁, hA l₁ W₁ hle₁, (Places.comap_cast_eq W₁).symm⟩
        ⟨Ideal.comap_isPrime _ W₂, hA l₂ W₂ hle₂, by rw [heq']; exact (Places.comap_cast_eq W₂).symm⟩
    have hm₁ := Places.comap_C_comap_eq (O := O l₁) (m l₁) hp₁
      (Places.maximal_le_of_C_mem (hp0 l₁) hp₁ hc₁)
    have hm₂ := Places.comap_C_comap_eq (O := O l₂) (m l₂) hp₂
      (Places.maximal_le_of_C_mem (hp0 l₂) hp₂ hc₂)
    have hl : l₁ = l₂ := hminj (by rw [← hm₁, ← hm₂, hWA])
    subst hl
    have := Places.eq_of_comap_eq (O := O l₁) (m l₁) hWA
    subst this
    rfl
  · intro W hW
    obtain ⟨hfin, hc⟩ := Finset.mem_filter.mp hW
    have hne : divCycle (mCoordIdeal y) f W ≠ 0 := hfinZ.mem_toFinset.mp hfin
    obtain ⟨hmin, hrel⟩ := Places.mem_of_divCycle_ne_zero hne
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨WA, ⟨hWAp, hWAle, hWAc⟩, -⟩ := hlift W hWp hrel (le_sup_left.trans hmin.1.2)
    have hpn : ((p : ℕ) : A) ∈ WA.comap (C : A →+* MRing ι A) := by
      rw [← hWAc, Ideal.mem_comap, MvPolynomial.map_C] at hc
      simpa [Ideal.mem_comap] using hc
    obtain ⟨l, hl⟩ := (hm _ (Ideal.comap_isPrime _ WA)).1 hpn
    obtain ⟨W', hW'p, hW'c⟩ := Places.exists_prime_of_comap_C (O := O l) (m l) hWAp hl.symm
    have hcomp : W'.comap (MvPolynomial.map (Int.castRingHom (O l))) = W := by
      rw [Places.comap_cast_eq (A := A), hW'c, hWAc]
    have hrel' : IsRelevant W' := Places.isRelevant_of_comap (Int.castRingHom (O l)) (hcomp ▸ hrel)
    have hle' : pointIdeal (O l) y ≤ W' := by
      rw [(hmod l).1]
      exact Ideal.map_le_iff_le_comap.mpr (hW'c ▸ hWAle)
    refine ⟨⟨l, W'⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨(hfinl l).mem_toFinset.mpr ?_, (hCp l W').1 (hcomp ▸ hc)⟩⟩, hcomp⟩
    rw [Function.mem_support, hmult l W' hW'p hrel' hle', hcomp]
    exact hne
  · rintro ⟨l, W⟩ hx
    obtain ⟨hne, hc⟩ := hmem l W (Finset.mem_sigma.mp hx).2
    obtain ⟨hWp, hrel, hle, hmh⟩ := hfacts l W hne
    dsimp only
    rw [hmult l W hWp hrel hle, GlobalTheory.T.residue_model_at_prime K ι Ω y A hconst (p : ℕ) (m l) (O l) (hpm l) (fd l) (hfd l) W
      hWp hmh hle (Places.maximal_le_of_C_mem (hp0 l) hWp hc) L]
    ring
