import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDegreeFibre
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightedHomogeneousComponentMap
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Generic

open NumbersDVR

theorem FibreDegreeSum.intNum_eq_cycEval (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (e : ℕ) (a : Fin e → K → ℤ) (p : ℕ)
    [Fact p.Prime] (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
      NumbersDVR.cycEval (fun W ↦ intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a)
        (NumbersDVR.divCycle P (C (p : ℤ))) := by
  classical
  have hp : p.Prime := Fact.out
  have hPprime : P.IsPrime := hP.2.1.1
  have hhor : ∀ r : ℤ, (C r : MRing ι ℤ) ∈ P → r = 0 := by
    intro r hr
    have hr' : r ∈ P.comap (C : ℤ →+* MRing ι ℤ) := hr
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at hr'
    exact (Ideal.mem_bot).mp hr'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)} with h𝔭def
  have h𝔭max : 𝔭.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have h𝔭 : 𝔭.IsPrime := h𝔭max.isPrime
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rw [h𝔭def, Ne, Ideal.span_singleton_eq_bot]
    exact hpZ.ne_zero
  let O := Localization.AtPrime 𝔭
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ h𝔭0 O
  let ϖ : O := (p : O)
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 O]
    change Ideal.map (algebraMap ℤ O) (Ideal.span {(p : ℤ)}) = _
    rw [Ideal.map_span, Set.image_singleton]
    simp [ϖ]
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  let M : Submonoid (MRing ι ℤ) := 𝔭.primeCompl.map (C (σ := Σ k, ι k))
  let φ := algebraMap (MRing ι ℤ) (MRing ι O)
  let P' : Ideal (MRing ι O) := P.map φ

  have hPdisj : Disjoint (M : Set (MRing ι ℤ)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrP
    have h0 := hhor r hrP
    rw [h0] at hr
    exact hr 𝔭.zero_mem
  have hP'prime : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (MRing ι O) P hPprime hPdisj
  have hP'comap : P'.comap φ = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι O) hPprime hPdisj
  have hmp : IsMultiProjPrime P' :=
    { isPrime := hP'prime
      multiHomog := WeightedDegree.isMultiHomogIdeal_map 𝔭.primeCompl
        ((Bridge.isMultiHomogIdeal_iff P).mpr hP.2.1.2.1)
      relevant := fun k ↦ by
        obtain ⟨i, hi⟩ := hP.2.1.2.2 k
        refine ⟨i, fun h ↦ hi ?_⟩
        have h' : φ (X ⟨k, i⟩) ∈ P' := by
          rw [show φ (X ⟨k, i⟩) = X ⟨k, i⟩ from map_X _ _]
          exact h
        have h'' : (X ⟨k, i⟩ : MRing ι ℤ) ∈ P'.comap φ := h'
        rw [hP'comap] at h''
        exact h'' }
  have hnt : P'.comap (C : O →+* MRing ι O) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_bot]
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalization.surj 𝔭.primeCompl x
    simp only at hms
    have hmem : φ (C m) ∈ P' := by
      rw [show φ (C m) = C (algebraMap ℤ O m) from map_C _ _, ← hms, map_mul]
      exact P'.mul_mem_right _ hx
    have hmem' : (C m : MRing ι ℤ) ∈ P'.comap φ := hmem
    rw [hP'comap] at hmem'
    have hm0 : m = 0 := hhor m hmem'
    rw [hm0, map_zero] at hms
    exact ((IsLocalization.map_units O s).mul_left_eq_zero).mp hms
  have hdimle : ringKrullDim (MRing ι O ⧸ P') ≤ ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    (WeightedDegree.ringKrullDim_quotient_map_le 𝔭.primeCompl P).trans_eq hP.2.2.2

  have key := ConservationOfNumberLE.proof.{0} IntNumAssoc.full SpecialCycleEval.full
    SpecialPieceRank.full GenericPieceRank.full SpecialIdealMultiHomog.full O ϖ hϖ K ι P' e hmp hnt
    hdimle a

  have hinjO : Function.Injective (Int.castRingHom O) := by
    rw [RingHom.ext_int (Int.castRingHom O) (algebraMap ℤ O)]
    exact IsLocalization.injective O 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (FractionRing O) := WeightedDegree.charZero_fractionRing O hinjO
  have hgen : gNum P' a = intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
    have hcomp : genFib P' = (P.map (MvPolynomial.map (Int.castRingHom ℚ))).map
        (MvPolynomial.map (algebraMap ℚ (FractionRing O))) := by
      unfold genFib
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold gNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ (FractionRing O) K ι _).2 e a

  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [show ((p : ℕ) : IsLocalRing.ResidueField O) = IsLocalRing.residue O ϖ by simp [ϖ],
        IsLocalRing.residue_eq_zero_iff, hmax]
      exact Ideal.subset_span rfl)
  let : Algebra (ZMod p) (IsLocalRing.ResidueField O) :=
    (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField O)).toAlgebra
  have hspec : ∀ W : Ideal (MRing ι ℤ), vNum (W.map φ) a =
      intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a := by
    intro W
    have hcomp : specialIdeal (W.map φ) = (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))) := by
      unfold specialIdeal
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold vNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 (ZMod p) (IsLocalRing.ResidueField O) K ι _).2 e a

  have hWdisj : ∀ W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MRing ι ℤ)}).minimalPrimes,
      Disjoint (M : Set (MRing ι ℤ)) W := by
    intro W hW
    have : W.IsPrime := hW.1.1
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrW
    have hle : 𝔭 ≤ W.comap (C : ℤ →+* MRing ι ℤ) := by
      rw [h𝔭def, Ideal.span_le, Set.singleton_subset_iff]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have heq := h𝔭max.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* MRing ι ℤ) W).ne_top hle
    have hr' : r ∈ W.comap (C : ℤ →+* MRing ι ℤ) := hrW
    rw [← heq] at hr'
    exact hr hr'
  have hmain := WeightedDegree.cycEval_divCycle_map (R' := O) 𝔭.primeCompl P (C (p : ℤ)) hWdisj
    (fun W' : Ideal (MRing ι O) ↦ vNum W' a)
  have hCp : (C ϖ : MRing ι O) = φ (C (p : ℤ)) := by
    rw [show φ (C (p : ℤ)) = C (algebraMap ℤ O (p : ℤ)) from map_C _ _]
    simp [ϖ]
  calc intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a = gNum P' a := hgen.symm
    _ = NumbersDVR.cycEval (fun W ↦ vNum W a) (NumbersDVR.divCycle P' (C ϖ)) := key.symm
    _ = NumbersDVR.cycEval (fun W ↦ vNum W a) (NumbersDVR.divCycle P' (φ (C (p : ℤ)))) := by rw [hCp]
    _ = NumbersDVR.cycEval (fun W ↦ vNum (W.map φ) a) (NumbersDVR.divCycle P (C (p : ℤ))) := hmain.symm
    _ = _ := by
      congr 1
      funext W
      exact hspec W

end Generic

open ReciprocityTheory.ChartRestriction.G

theorem FibreDegreeSum.proof : FibreDegreeSum.Statement := by
  intro K _ _ ι _ P e a p hP hp
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [FibreDegreeSum.intNum_eq_cycEval K ι P e a p hP, NumbersDVR.cycEval, finsum_mem_def]
  refine finsum_congr fun W ↦ ?_
  by_cases hW : W ∈ Geo.divSupp P (C (p : ℤ))
  · rw [Set.indicator_of_mem hW]
    have hW' : W ∈ (P ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W := hW
    have hWp : W.IsPrime := hW.1.1.1
    have hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W :=
      hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hC : Geo.IsMultiHomog (C (p : ℤ) : Geo.MRing ι) 0 := by
      intro m hm k
      have h0 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h0
      split_ifs at h0 with h
      · subst h
        simp
      · exact absurd rfl h0
    have hMP : Geo.IsMultiProjPrime W :=
      ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1.2.1 hC hW.1, hW.2⟩
    have hdimW : ringKrullDim (Geo.MRing ι ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      refine FibreCompDimZ.full (Σ k, ι k) P hP.2.1.1 hP.2.2.1 (e + Fintype.card K) p hp ?_ W hW.1
      rw [show e + Fintype.card K + 1 = e + 1 + Fintype.card K by omega]
      exact hP.2.2.2
    have hm : Geo.multAt (P ⊔ Ideal.span {C (p : ℤ)}) W =
        (NumbersDVR.multAt (P ⊔ Ideal.span {C (p : ℤ)}) W).toNat :=
      Bridge.multAt_eq_toNat _ _
    rw [NumbersDVR.divCycle, dif_pos hW', hm, Bridge.intNum_map_eq_geoNum p e W hMP hpW hdimW a]
  · have hW' : ¬(W ∈ (P ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W) := hW
    rw [Set.indicator_of_notMem hW, NumbersDVR.divCycle, dif_neg hW', zero_mul]

end

end GroundTheory.Heights₂.Heights.Targets
