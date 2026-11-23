import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSectionTools

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.PlaceModel

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

theorem map_mem_iff {A O : Type} [CommRing A] [CommRing O] [Algebra A O] [Algebra A Ω] [Algebra O Ω]
    [IsScalarTower A O Ω] {f : MRing ι A} :
    MvPolynomial.map (algebraMap A O) f ∈ pointIdeal O y ↔ f ∈ pointIdeal A y := by
  rw [pointIdeal, pointIdeal, RingHom.mem_ker, RingHom.mem_ker]
  simp only [pointConeMap]
  rw [MvPolynomial.aeval_map_algebraMap]

theorem cast_mem_iff [Fintype K] [∀ k, Fintype (ι k)] {O : Type} [CommRing O] [Algebra O Ω]
    {f : MRing ι ℤ} :
    MvPolynomial.map (Int.castRingHom O) f ∈ pointIdeal O y ↔ f ∈ mCoordIdeal y := by
  have h : algebraMap ℤ O = Int.castRingHom O := RingHom.ext_int _ _
  rw [← h, map_mem_iff]
  rfl

section Place

variable {A O : Type} [CommRing A] [CommRing O] [Algebra A O] (m : Ideal A) [m.IsPrime]
  [IsLocalization.AtPrime O m]

include m in

theorem injective_toField [Algebra A Ω] [Algebra O Ω] [IsScalarTower A O Ω]
    (hA : Function.Injective (algebraMap A Ω)) : Function.Injective (algebraMap O Ω) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj m.primeCompl a
  have hs' : a * algebraMap A O s = algebraMap A O x := hs
  have hx : algebraMap A Ω x = 0 := by
    rw [IsScalarTower.algebraMap_apply A O Ω, ← hs', map_mul, ha, zero_mul]
  have hx0 : x = 0 := hA (by rw [hx, map_zero])
  rw [hx0, map_zero] at hs'
  have hu : IsUnit (algebraMap A O s) := IsLocalization.map_units O s
  first
    | exact hu.mul_left_eq_zero.1 hs'
    | exact hu.mul_right_eq_zero.1 hs'

include m in

theorem pointIdeal_eq_map [Algebra A Ω] [Algebra O Ω] [IsScalarTower A O Ω] :
    pointIdeal O y = (pointIdeal A y : Ideal (MRing ι A)).map (MvPolynomial.map (algebraMap A O)) := by
  refine le_antisymm (fun g hg => ?_) (Ideal.map_le_iff_le_comap.2 fun f hf => Ideal.mem_comap.2 (map_mem_iff.2 hf))
  haveI : IsLocalization (m.primeCompl.map (C : A →+* MRing ι A)) (MRing ι O) :=
    MvPolynomial.isLocalization _ _
  obtain ⟨⟨f, s⟩, hs⟩ := IsLocalization.surj (m.primeCompl.map (C : A →+* MRing ι A)) g
  have hs' : g * MvPolynomial.map (algebraMap A O) (s : MRing ι A) =
      MvPolynomial.map (algebraMap A O) f := hs
  have hf : f ∈ pointIdeal A y :=
    map_mem_iff.1 (by rw [← hs']; exact Ideal.mul_mem_right _ _ hg)
  have hu : IsUnit (MvPolynomial.map (algebraMap A O) (s : MRing ι A)) :=
    IsLocalization.map_units (MRing ι O) s
  exact (Ideal.mul_unit_mem_iff_mem _ hu).1 (by rw [hs']; exact Ideal.mem_map_of_mem _ hf)

include m in

theorem isAlgebraic_int [IsDomain A] [Module.Finite ℤ A] : Algebra.IsAlgebraic ℤ O := by
  haveI : Algebra.IsAlgebraic A O := IsLocalization.isAlgebraic O m.primeCompl
  exact Algebra.IsAlgebraic.trans ℤ A O

end Place

theorem trdeg_eq {O : Type} [CommRing O] [IsDomain O] [Algebra.IsAlgebraic ℤ O]
    {P : Ideal (MRing ι ℤ)} {Q : Ideal (MRing ι O)} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hQP : Q.comap (MvPolynomial.map (Int.castRingHom O)) = P)
    (hCP : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) (hCQ : Q.comap (C : O →+* MRing ι O) = ⊥) :
    Algebra.trdeg O (MRing ι O ⧸ Q) = Algebra.trdeg ℤ (MRing ι ℤ ⧸ P) := by
  haveI := hP
  haveI := hQ
  let φ : (MRing ι ℤ ⧸ P) →+* (MRing ι O ⧸ Q) :=
    Ideal.quotientMap Q (MvPolynomial.map (Int.castRingHom O)) hQP.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hQP.le
  let _ : Algebra (MRing ι ℤ ⧸ P) (MRing ι O ⧸ Q) := φ.toAlgebra
  have : @IsScalarTower ℤ (MRing ι ℤ ⧸ P) (MRing ι O ⧸ Q)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : @IsScalarTower ℤ O (MRing ι O ⧸ Q) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : FaithfulSMul (MRing ι ℤ ⧸ P) (MRing ι O ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have hZ : Function.Injective (algebraMap ℤ (MRing ι ℤ ⧸ P)) := by
    refine (injective_iff_map_eq_zero (algebraMap ℤ (MRing ι ℤ ⧸ P))).2 fun a ha => ?_
    have h : (C a : MRing ι ℤ) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using ha)
    have h' : a ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [hCP] at h'
    exact (Submodule.mem_bot _).1 h'
  have : @FaithfulSMul ℤ (MRing ι ℤ ⧸ P) Algebra.toSMul :=
    (faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ℤ ⧸ P)).2 hZ
  have hOB : Function.Injective (algebraMap O (MRing ι O ⧸ Q)) := by
    refine (injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ Q))).2 fun a ha => ?_
    have h : (C a : MRing ι O) ∈ Q :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk Q (C a) = 0 from ha)
    have h' : a ∈ Q.comap (C : O →+* MRing ι O) := h
    rw [hCQ] at h'
    exact (Submodule.mem_bot _).1 h'
  have : FaithfulSMul O (MRing ι O ⧸ Q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hOB
  have hZO : Function.Injective (algebraMap ℤ O) := by
    refine (injective_iff_map_eq_zero (algebraMap ℤ O)).2 fun a ha => ?_
    have h : MvPolynomial.map (Int.castRingHom O) (C a : MRing ι ℤ) ∈ Q := by
      rw [map_C]
      have e : Int.castRingHom O a = 0 := by simpa using ha
      rw [e, map_zero]
      exact Q.zero_mem
    have h1 : (C a : MRing ι ℤ) ∈ P := by
      rw [← hQP]
      exact h
    have h' : a ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h1
    rw [hCP] at h'
    exact (Submodule.mem_bot _).1 h'
  have : @FaithfulSMul ℤ O Algebra.toSMul := (faithfulSMul_iff_algebraMap_injective ℤ O).2 hZO
  have hφZ : Function.Injective (algebraMap ℤ (MRing ι O ⧸ Q)) := by
    rw [IsScalarTower.algebraMap_eq ℤ O (MRing ι O ⧸ Q)]
    exact hOB.comp hZO
  have : Algebra.IsAlgebraic (MRing ι ℤ ⧸ P) (MRing ι O ⧸ Q) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    induction g using MvPolynomial.induction_on with
    | C a =>
      have h1 : IsAlgebraic ℤ (algebraMap O (MRing ι O ⧸ Q) a) :=
        (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic ℤ a).algebraMap
      exact h1.extendScalars hZ
    | add f g hf hg =>
      rw [map_add]
      exact hf.add hg
    | mul_X f i hf =>
      rw [map_mul]
      refine hf.mul ?_
      have e : Ideal.Quotient.mk Q (X i) =
          algebraMap (MRing ι ℤ ⧸ P) (MRing ι O ⧸ Q) (Ideal.Quotient.mk P (X i)) := by
        change _ = φ _
        simp only [φ, Ideal.quotientMap_mk, map_X]
      rw [e]
      exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq ℤ O (A := MRing ι O ⧸ Q)
  have h2 := trdeg_add_eq ℤ (MRing ι ℤ ⧸ P) (A := MRing ι O ⧸ Q)
  rw [trdeg_eq_zero (R := ℤ) (A := O), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι ℤ ⧸ P) (A := MRing ι O ⧸ Q), add_zero] at h2
  exact h1.trans h2.symm

variable [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]

theorem comap_C_pointIdeal (hO : Function.Injective (algebraMap O Ω)) :
    (pointIdeal O y : Ideal (MRing ι O)).comap (C : O →+* MRing ι O) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h0 : pointConeMap O y (C a) = 0 := ha
  simp only [pointConeMap, aeval_C, MvPolynomial.algebraMap_apply] at h0
  have h1 : algebraMap O Ω a = 0 := MvPolynomial.C_injective K Ω (by simpa using h0)
  exact (Submodule.mem_bot _).2 (hO (by rw [h1, map_zero]))

theorem isModelOver_pointIdeal [Algebra.IsAlgebraic ℤ O] (hO : Function.Injective (algebraMap O Ω))
    {D : ℕ} (h : IsArithVar (mCoordIdeal y) (D + 1)) : IsModelOver (pointIdeal O y) D := by
  have h' := h
  obtain ⟨-, hmp, hC, -⟩ := h'
  have hC' : (mCoordIdeal y).comap (C : ℤ →+* MRing ι ℤ) = ⊥ := hC
  have hP : (mCoordIdeal y).IsPrime := hmp.1
  have hn := comap_C_pointIdeal (ι := ι) (y := y) hO
  have hcomap : (pointIdeal O y).comap (MvPolynomial.map (Int.castRingHom O)) = mCoordIdeal y := by
    ext f
    rw [Ideal.mem_comap]
    exact cast_mem_iff
  have hm : IsMultiProjPrime (pointIdeal O y) :=
    ⟨pointIdeal_isPrime y, SegreFlagCutChartSection.isMultiHomogIdeal_pointIdeal y, fun k => by
      obtain ⟨i, hi⟩ := hmp.2.2 k
      exact ⟨i, fun hx => hi (cast_mem_iff (O := O).1 (by rwa [map_X]))⟩⟩
  obtain ⟨p⟩ : Nonempty Nat.Primes := ⟨⟨2, Nat.prime_two⟩⟩
  have hmz := ZpModel.isModelOver_extTo p h
  have hdz := DvrConeDimTrdeg.proof (ZP p) K ι _ hmz.multiProj hmz.noTorsion
  have htz := ZpModel.trdeg_eq p hP hC'
  refine ⟨hm, hn, ?_⟩
  rw [DvrConeDimTrdeg.proof O K ι _ hm hn, trdeg_eq hP (pointIdeal_isPrime y) hcomap hC' hn, ← htz,
    ← hdz, hmz.dim]

theorem eq_bot_of_irreducible_notMem {c : Ideal O} (hc : c.IsPrime) {ϖ : O} (hϖ : Irreducible ϖ)
    (h : ϖ ∉ c) : c = ⊥ := by
  by_contra hne
  have hmax : c.IsMaximal := hc.isMaximal hne
  apply h
  rw [IsLocalRing.eq_maximalIdeal hmax]
  exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit

theorem isVert_map {D : ℕ} (h : IsArithVar (mCoordIdeal y) (D + 1)) {ϖ : O} (hϖ : Irreducible ϖ)
    {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hT : T.IsVertOff (mCoordIdeal y) S) :
    (T.map (Int.castRingHom O)).IsVert (pointIdeal O y) ϖ := by
  intro i
  obtain ⟨⟨bf, bg, hbf, hbg, hb⟩, hf, hg, hu⟩ := hT i
  have hC' : (mCoordIdeal y).comap (C : ℤ →+* MRing ι ℤ) = ⊥ := h.2.2.1
  have hhom : ∀ {f : MRing ι ℤ} {b : K → ℕ}, IsMultiHomog f b →
      IsMultiHomog (MvPolynomial.map (Int.castRingHom O) f) b := by
    intro f b h d hd
    refine h fun h0 => hd ?_
    rw [coeff_map, h0, map_zero]
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, hhom hbf, hhom hbg, hb⟩
    (fun h => hf (cast_mem_iff.1 h)) (fun h => hg (cast_mem_iff.1 h)) ?_
  intro W hW hPW hrel hϖW
  have hWp : (W.comap (MvPolynomial.map (Int.castRingHom O))).IsPrime := Ideal.comap_isPrime _ _
  have hPW' : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom O)) :=
    fun x hx => hPW (cast_mem_iff.2 hx)
  have hrelW : IsRelevant (W.comap (MvPolynomial.map (Int.castRingHom O))) := by
    intro k
    obtain ⟨j, hj⟩ := hrel k
    refine ⟨j, fun h => hj ?_⟩
    have h' : MvPolynomial.map (Int.castRingHom O) (X ⟨k, j⟩ : MRing ι ℤ) ∈ W := h
    rwa [map_X] at h'
  have hbot : W.comap (C : O →+* MRing ι O) = ⊥ :=
    eq_bot_of_irreducible_notMem (Ideal.comap_isPrime _ _) hϖ hϖW
  have hoff : ∀ q ∈ S, (C ((q : ℕ) : ℤ) : MRing ι ℤ) ∉
      W.comap (MvPolynomial.map (Int.castRingHom O)) := by
    intro q _ hq
    have hq' : MvPolynomial.map (Int.castRingHom O) (C ((q : ℕ) : ℤ) : MRing ι ℤ) ∈ W := hq
    rw [map_C] at hq'
    have h0 : Int.castRingHom O ((q : ℕ) : ℤ) ∈ W.comap (C : O →+* MRing ι O) := hq'
    rw [hbot] at h0
    have h1 : Int.castRingHom O ((q : ℕ) : ℤ) = 0 := (Submodule.mem_bot _).1 h0
    have h2 : (C ((q : ℕ) : ℤ) : MRing ι ℤ) ∈ mCoordIdeal y := by
      refine cast_mem_iff (O := O).1 ?_
      rw [map_C, h1, map_zero]
      exact Ideal.zero_mem _
    have h3 : ((q : ℕ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι ℤ) := h2
    rw [hC'] at h3
    have h4 : ((q : ℕ) : ℤ) = 0 := (Submodule.mem_bot _).1 h3
    exact q.2.ne_zero (by exact_mod_cast h4)
  obtain ⟨u, v, huW, hvW, huv⟩ := hu _ hWp hPW' hrelW hoff
  refine ⟨MvPolynomial.map (Int.castRingHom O) u, MvPolynomial.map (Int.castRingHom O) v,
    huW, hvW, ?_⟩
  have h5 := cast_mem_iff (O := O).2 huv
  rw [map_sub, map_mul, map_mul] at h5
  exact h5

end

end GlobalTheory.CompanionTheory.Ar.Num.PlaceModel

theorem GlobalTheory.CompanionTheory.Ar.Num.pl_model : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], pointIdeal O y = (pointIdeal A y).map (MvPolynomial.map (algebraMap A O)) ∧ IsModelOver (pointIdeal O y) D ∧ ∀ (ϖ : O), Irreducible ϖ → ∀ (σ : Type) (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff (mCoordIdeal y) S → (T.map (Int.castRingHom O)).IsVert (pointIdeal O y) ϖ := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hinj _ D h m _ O _ _ _ _ _ _ _
  haveI : Algebra.IsAlgebraic ℤ O := PlaceModel.isAlgebraic_int m
  exact ⟨PlaceModel.pointIdeal_eq_map m, PlaceModel.isModelOver_pointIdeal
    (PlaceModel.injective_toField m hinj) h, fun ϖ hϖ σ S T hT => PlaceModel.isVert_map h hϖ hT⟩
