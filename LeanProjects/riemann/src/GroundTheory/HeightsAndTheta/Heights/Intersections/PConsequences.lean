import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_congr_pts (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl

theorem cycR_sub_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring

theorem tensor_sqMetric_a {A : HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring

theorem ArithmeticIntersectionSecond.proof : ArithmeticIntersectionSecond.Statement := metricChange

theorem Conservation.proof : Conservation.Statement := Conservation.statement_holds

theorem InductiveIntersectionFormula.proof : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith

theorem ArithmeticIntersectionFifth.proof (h₀ : ArithVarZeroStatement) : ArithmeticIntersectionFifth.Statement := by
  intro K _ ι _ I hI P A s hP hA ⟨a, ha, hs, hsP⟩
  have hR := hI.2.2 P 0 Fin.elim0 A s a hP (fun j ↦ j.elim0) hA ha hs hsP
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) A : Fin (0 + 1) → HermLine ι) = ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc] at hR
  rw [hR, recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW ↦ ?_
  have hnh : ¬ IsHorizontal W := fun hh ↦
    h₀ K ι W ((divSuppArith K ι P 0 A s W hP ⟨a, ha, hs, hsP⟩ hW).1 hh)
  rw [if_neg hnh, if_neg hnh]

theorem ae_eval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem RatR.proof (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith

end GroundTheory.Heights₂.Heights.Inter
