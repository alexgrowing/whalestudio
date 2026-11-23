import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointMultiplicity

variable {K : Type} {ι : K → Type}

theorem aeval_mul_of_homog [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical
  rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]

theorem map_aeval_int {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CurveVerticalPointMultiplicity

open CurveVerticalPointMultiplicity GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart in

theorem CurveVertPointMultChart.proof (hCh : CurveVertPointChart.Statement)
    (hN : CurveVertPointNagata.Statement) : CurveVertPointMultChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN K ι Ω y s d hP hs hsP W hW c hc a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let e : Localization.AtPrime (curvePtIdeal y W) →+* Ω := IsLocalization.lift hunit
  have hinj : Function.Injective e := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl)
      (Localization.AtPrime (curvePtIdeal y W)) (le_nonZeroDivisors_of_noZeroDivisors fun h =>
        h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  let r : (Σ k, ι k) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p) (⟨b' p, hb' p⟩ : (curvePtIdeal y W).primeCompl)
  have her : ∀ p, e (r p) = y p / y ⟨p.1, c p.1⟩ := fun p =>
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' p).symm
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [map_aeval_int, funext her]
    have key : aeval y s = aeval (fun p => y p / y ⟨p.1, c p.1⟩) s * ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [← aeval_mul_of_homog _ (fun k => y ⟨k, c k⟩) hs]
      exact congrArg (fun v => aeval v s) (funext fun p => (div_mul_cancel₀ _ (hyc p.1)).symm)
    have hpc : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : Ω) = (b : Ω) * _
    apply mul_right_cancel₀ hpc
    rw [mul_assoc, ← key, hab]

  have hXk : ∀ k, (X k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl := fun k h => by
    have h1 := MvPolynomial.mem_map_C_iff.mp h (Finsupp.single k 1)
    rw [MvPolynomial.coeff_X, if_pos rfl] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hprod : (∏ k, X k ^ d k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl :=
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hXk k) _
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) := by
    rw [hΦ s, aeval_mul_of_homog (fun p => MvPolynomial.C (r p)) X hs, ← map_aeval_int MvPolynomial.C, hsr,
      IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, ← mul_assoc,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), MvPolynomial.algebraMap_eq]
  have hv : IsUnit (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) :=
    ((hbu.map MvPolynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hprod⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), ← Ideal.map_map,
      MvPolynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dif_pos hWp, locLen, dif_pos hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights.Targets
