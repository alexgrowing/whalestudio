import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arInt_mul (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  obtain ⟨b, -, htb, htP⟩ := id ht
  show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP]
      with y hys hyt
    rw [← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)
      ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hsh := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hsh.2.1
      have hs0 := norm_pos_iff.mpr (hys z hz hsh.2.2)
      have ht0 := norm_pos_iff.mpr (hyt z hz hsh.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← add_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) +
          Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)
      rw [map_mul, map_mul, norm_mul, mul_div_mul_comm]
      exact Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'
    · simp
  · simp

theorem RMul.proof (hInt : PtsIntegrableStatement) : RMulStatement := by
  intro K _ ι _ I P n L A B s t hP hL hA hB hs ht
  obtain ⟨-, -, -, hsP⟩ := id hs
  obtain ⟨-, -, -, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 L hsP htP, arInt_mul hInt hP hL hA hB hs ht]
  ring

end GroundTheory.Heights₂.Heights.Inter
