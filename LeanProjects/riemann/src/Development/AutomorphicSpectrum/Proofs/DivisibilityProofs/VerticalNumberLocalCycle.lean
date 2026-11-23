import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionNumberFieldEquiv
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivCycleMapLocalisation
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontalStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.ZpVert

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem nonempty_residue_equiv (p : Nat.Primes) [Fact (p : ℕ).Prime] :
    Nonempty (ZMod (p : ℕ) ≃+* IsLocalRing.ResidueField (ZP p)) := by
  haveI hmax : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero)
  exact ⟨(Int.quotientSpanNatEquivZMod (p : ℕ)).symm.trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {((p : ℕ) : ℤ)}) (ZP p))⟩

theorem map_extTo {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (Q : Ideal (MRing ι ℤ)) :
    (extTo R Q).map (MvPolynomial.map g) = extTo S Q := by
  unfold extTo
  rw [Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp
  · simp

theorem vNumL_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    [Fact (p : ℕ).Prime] (Q : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) :
    vNumL (extTo (ZP p) Q) l = intNumL (ZMod (p : ℕ)) (extTo (ZMod (p : ℕ)) Q) l := by
  obtain ⟨e⟩ := nonempty_residue_equiv p
  have h : specialIdeal (extTo (ZP p) Q) =
      (extTo (ZMod (p : ℕ)) Q).map (MvPolynomial.map (e : ZMod (p : ℕ) →+* _)) := by
    unfold specialIdeal
    rw [map_extTo, map_extTo]
  have h2 := intNumL_map_ringEquiv K ι (ZMod (p : ℕ)) (IsLocalRing.ResidueField (ZP p)) e
    (extTo (ZMod (p : ℕ)) Q) l
  rw [← h2, ← h]
  rfl

theorem divCycle_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) (W' : Ideal (MRing ι (ZP p))) (hW' : W'.IsPrime) :
    divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' =
      divCycle P f (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := by
  have h := divCycle_map_localisation K ι ℤ (ZP p) (Ideal.span {((p : ℕ) : ℤ)}).primeCompl P f W' hW'
  have e : algebraMap ℤ (ZP p) = Int.castRingHom (ZP p) := RingHom.ext_int _ _
  rw [e] at h
  exact h

theorem isPrime_of_ne {R : Type} [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc.1.1.1
  · exact absurd rfl h

theorem disjoint_consts_of_mem (p : Nat.Primes) {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    Disjoint (ZpModel.consts ι p : Set (MRing ι ℤ)) (W : Set (MRing ι ℤ)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨s, hs, rfl⟩ hmem
  have hs' : s ∉ Ideal.span {((p : ℕ) : ℤ)} := hs
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ s := fun h => hs' (Ideal.mem_span_singleton.2 h)
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.1 p.2).irreducible.coprime_iff_not_dvd.2 hdvd
  have h1 : (C (u * ((p : ℕ) : ℤ) + v * s) : MRing ι ℤ) ∈ W := by
    rw [C_add, C_mul, C_mul]
    exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hmem)
  rw [huv, C_1] at h1
  exact hW.ne_top ((Ideal.eq_top_iff_one W).2 h1)

theorem finsum_eq_mem {α : Type*} (g : α → ℤ) (t : Set α) (h : Function.support g ⊆ t) :
    ∑ᶠ x, g x = ∑ᶠ x ∈ t, g x := by
  rw [← finsum_mem_univ g]
  refine finsum_mem_inter_support_eq g _ _ ?_
  rw [Set.univ_inter, Set.inter_eq_right.2 h]

theorem extTo_comap (p : Nat.Primes) (W' : Ideal (MRing ι (ZP p))) :
    extTo (ZP p) (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) = W' := by
  haveI := ZpModel.isLocalization_consts ι p
  rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
  exact IsLocalization.map_comap (ZpModel.consts ι p) (MRing ι (ZP p)) W'

theorem bijOn_comap [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) :
    Set.BijOn (fun W' : Ideal (MRing ι (ZP p)) => W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))))
      {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}
      {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W} := by
  have hCmap : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) := by
    rw [map_C]
    simp
  haveI := ZpModel.isLocalization_consts ι p
  refine ⟨?_, ?_, ?_⟩
  · rintro W' ⟨hW', hp⟩
    refine ⟨?_, ?_⟩
    · rw [← divCycle_extTo p P f W' (isPrime_of_ne hW')]
      exact hW'
    · show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rwa [hCmap]
  · rintro W₁ - W₂ - h
    calc W₁ = extTo (ZP p) (W₁.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := (extTo_comap p W₁).symm
      _ = extTo (ZP p) (W₂.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := congrArg _ h
      _ = W₂ := extTo_comap p W₂
  · rintro W ⟨hW, hp⟩
    have hWp : W.IsPrime := isPrime_of_ne hW
    have hd := disjoint_consts_of_mem p hWp hp
    have hprime : (extTo (ZP p) W).IsPrime := by
      rw [ZpModel.extTo_eq]
      exact IsLocalization.isPrime_of_isPrime_disjoint (ZpModel.consts ι p) _ W hWp hd
    have hcomap : (extTo (ZP p) W).comap (MvPolynomial.map (Int.castRingHom (ZP p))) = W := by
      have h := IsLocalization.under_map_of_isPrime_disjoint (ZpModel.consts ι p) (MRing ι (ZP p)) hWp hd
      rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
      exact h
    refine ⟨extTo (ZP p) W, ⟨?_, ?_⟩, hcomap⟩
    · rw [divCycle_extTo p P f _ hprime, hcomap]
      exact hW
    · rw [← hCmap]
      exact Ideal.mem_map_of_mem _ hp

end

end GlobalTheory.CompanionTheory.Ar.Num.ZpVert

open GlobalTheory.CompanionTheory.Ar.Num.ZpVert in

theorem GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  intro K _ _ ι _ P D hP p a f hf hfP l hl
  classical
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨hirr, hmodel, -⟩ := zp_model K ι P D hP p
  have hfP' : MvPolynomial.map (Int.castRingHom (ZP p)) f ∉ extTo (ZP p) P :=
    fun h => hfP (ZpModel.mem_of_map_mem p hP.2.1.1 hP.2.2.1 h)
  have hf' : IsMultiHomog (MvPolynomial.map (Int.castRingHom (ZP p)) f) a := by
    intro d hd
    refine hf fun h0 => hd ?_
    rw [coeff_map, h0, map_zero]
  unfold vertAt cycList cycEval
  rw [finsum_eq_mem _ {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W},
    finsum_eq_mem _ {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}]
  · symm
    refine finsum_mem_eq_of_bijOn _ (bijOn_comap p P f) ?_
    rintro W' ⟨hW', hp⟩
    have hWp : W'.IsPrime := isPrime_of_ne hW'
    have hQp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))) := by
      show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rw [map_C]
      simpa using hp
    rw [divCycle_extTo p P f W' hWp]
    beta_reduce
    rw [if_pos hQp]
    congr 1
    have h := vNumL_extTo p (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) l
    rw [extTo_comap] at h
    exact h
  · intro W' hW'
    have h1 := left_ne_zero_of_mul hW'
    refine ⟨h1, ?_⟩
    by_contra hp
    have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal (ZP p) ((p : ℕ) : ZP p) hirr K ι (extTo (ZP p) P) D hmodel a _ hf' hfP' W' h1 hp l hl
    exact right_ne_zero_of_mul hW' h0
  · intro W hW
    have h1 := left_ne_zero_of_mul hW
    refine ⟨h1, ?_⟩
    by_contra hp
    exact right_ne_zero_of_mul hW (if_neg hp)
