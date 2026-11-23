import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRatSectionSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFormNonvanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc

theorem cycR_eq_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P X s) :
    cycR I P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  have hnh : ¬ IsHorizontal W := fun hh =>
    Inter.arithVarZero K ι W ((divSuppArith K ι P 0 X s W hP hs hW).1 hh)
  rw [if_neg hnh, if_neg hnh]

omit [∀ k, Fintype (ι k)] in

theorem snoc_elim0 (X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) X : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      fun _ => X := by
  funext j
  fin_cases j
  rfl

end CurveRationalSectionSum

open CurveRationalSectionSum in

theorem CurveRatSectionSum.proof (hNV : CurveFormNonvanishing.Statement) : CurveRatSectionSum.Statement := by
  intro K _ ι _ Ω _ y A II hII har hA n dg dh g h hg hh hd hgy hhy
  obtain ⟨-, hAdd, hR⟩ := hII K ι
  have hB := isSmoothHerm_sqMetric (ι := ι) dh
  have hnA := Inter.isSmoothHerm_hermZpow hA (n : ℤ)
  have hgP : g ∉ mCoordIdeal y := by
    rw [Inter.mCoordIdeal_eq_ker_multiConeMap]
    exact (Inter.DiagRAux.not_mem_ker_iff_aeval_ne y g dg hg).mpr hgy
  have hhP : h ∉ mCoordIdeal y := by
    rw [Inter.mCoordIdeal_eq_ker_multiConeMap]
    exact (Inter.DiagRAux.not_mem_ker_iff_aeval_ne y h dh hh).mpr hhy
  have hda : ∀ k, ((Inter.hermZpow A n).tensor (HermLine.sqMetric dh)).a k = dg k := fun k => by
    show (n : ℤ) • A.a k + (dh k : ℤ) = dg k
    rw [hd k, smul_eq_mul]
    ring
  have hRg := hR _ 0 Fin.elim0 _ g dg har (fun j => j.elim0)
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hnA hB) hda hg hgP
  have hRh := hR _ 0 Fin.elim0 _ h dh har (fun j => j.elim0) hB (fun k => rfl) hh hhP
  have hsum := hAdd _ 0 Fin.elim0 _ _ har (fun j => j.elim0) hnA hB
  have hpow : II K ι (mCoordIdeal y) 1 (fun _ => Inter.hermZpow A n) =
      (n : ℝ) ^ 1 * II K ι (mCoordIdeal y) 1 (fun _ => A) :=
    HilbertSamuel.Mono.fam_hermZpow (hII K ι) (D := 0) har hA n
  rw [recR_eq, cycR_eq_vertR _ har ⟨dg, hda, hg, hgP⟩, arInt_eq_sum har hda hg, snoc_elim0] at hRg
  rw [recR_eq, cycR_eq_vertR _ har (X := HermLine.sqMetric dh) ⟨dh, fun k => rfl, hh, hhP⟩, arInt_eq_sum har (X := HermLine.sqMetric dh) (fun k => rfl) hh,
    snoc_elim0] at hRh
  rw [snoc_elim0, snoc_elim0, snoc_elim0] at hsum
  rw [pow_one] at hpow
  have := HilbertSamuel.CurvePointsFinite.proof K ι _ har
  have hcomb : ∑ᶠ q : projPts (mCoordIdeal y),
        logNorm ((Inter.hermZpow A n).tensor (HermLine.sqMetric dh)) g (Quot.out q : mcPts (mCoordIdeal y)) -
      ∑ᶠ q : projPts (mCoordIdeal y), logNorm (HermLine.sqMetric dh) h (Quot.out q : mcPts (mCoordIdeal y)) =
      ∑ᶠ q : projPts (mCoordIdeal y), ratLogNormPow A n g h (Quot.out q : mcPts (mCoordIdeal y)) := by
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun q => ?_
    have hz := (Quot.out q).2
    have hg0 := norm_pos_iff.mpr (hNV K ι Ω y dg g har hg hgy _ hz)
    have hh0 := norm_pos_iff.mpr (hNV K ι Ω y dh h har hh hhy _ hz)
    have hA0 := A.pos _ hz.1
    have hB0 := (HermLine.sqMetric (ι := ι) dh).pos _ hz.1
    unfold logNorm ratLogNormPow
    show Real.log (_ / (A.h _ ^ (n : ℤ) * (HermLine.sqMetric dh).h _)) - Real.log (_ / (HermLine.sqMetric dh).h _) =
      Real.log (_ / (_ * A.h _ ^ n))
    rw [zpow_natCast, Real.log_div hg0.ne' (mul_pos (pow_pos hA0 n) hB0).ne',
      Real.log_mul (pow_pos hA0 n).ne' hB0.ne', Real.log_div hh0.ne' hB0.ne',
      Real.log_div hg0.ne' (mul_pos hh0 (pow_pos hA0 n)).ne', Real.log_mul hh0.ne' (pow_pos hA0 n).ne']
    ring
  have e1 : II K ι (mCoordIdeal y) 1 (fun _ => (Inter.hermZpow A n).tensor (HermLine.sqMetric dh)) =
      II K ι (mCoordIdeal y) 1 (fun _ => Inter.hermZpow A n) +
        II K ι (mCoordIdeal y) 1 (fun _ => HermLine.sqMetric dh) := hsum
  linarith

end

end GroundTheory.Heights₂.Heights.Targets
