import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogTwoXc
import GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtHorizontalEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cycles

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_of_mem_divSupp' {P W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp P f) : f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem mem_divSupp_mul_left' {P W : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hgP : g ∉ P) (hW : W ∈ divSupp P f) : W ∈ divSupp P (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le P f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hP hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgP hQW).ge

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_divSupp_of_mul' {P W : Ideal (MRing ι)} {f g : MRing ι}
    (hW : W ∈ divSupp P (f * g)) (hf : f ∈ W) : W ∈ divSupp P f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun _ hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le P f g).trans hQ.2⟩ hQW⟩, hW.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem multAt_eq' (J W : Ideal (MRing ι)) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

theorem divCycle_mul' {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hf : f ∉ P) (hg : g ∉ P) : divCycle P (f * g) = divCycle P f + divCycle P g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp P (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp P (g * f) := by rwa [mul_comm]
    have key := locLen_mul hP hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq' _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, multAt_eq' _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp' h2),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp' h2), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero (V := P) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp' h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left' hP hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left' hP hf h2)]

open Classical in

def cycWeight (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ}
    (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem cycR_eq_sum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by
  classical
  unfold cycR
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (s := (divCycle P s).support)]
  · refine Finset.sum_congr rfl fun W _ => ?_
    by_cases h : W ∈ divSupp P s
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe, cycWeight]
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hW
    by_cases h : W ∈ divSupp P s
    · have : multAt (P ⊔ Ideal.span {s}) W = 0 := by
        simpa [divCycle, Finsupp.ofSupportFinite_coe, h] using h0
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]

theorem cycR_mul (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {n : ℕ} (L : Fin n → HermLine ι) {s t : MRing ι} (hs : s ∉ P) (ht : t ∉ P) :
    cycR I P L (s * t) = cycR I P L s + cycR I P L t := by
  rw [cycR_eq_sum, cycR_eq_sum, cycR_eq_sum, divCycle_mul' hP hs ht]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

end Cycles

section NoHorizontal

theorem not_isHorizontal_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} {W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hs : IsSectionOn P A s)
    (hW : W ∈ divSupp P s) : ¬ IsHorizontal W := fun hh =>
  h0 K ι W ((divSuppArith K ι P 0 A s W hP hs hW).1 hh)

theorem eval_ne_zero_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : eval z (map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro hzero
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => ?_) ?_
    · rw [RingHom.mem_ker]
      exact hz.2 f hf
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact hzero
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel : IsRelevant W := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hX => hi ?_⟩
    have h1 := hWQ hX
    rw [RingHom.mem_ker] at h1
    simpa [φ] using h1
  have hhor : IsHorizontal W := by
    unfold IsHorizontal
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap] at hn
    have h1 := hWQ hn
    rw [RingHom.mem_ker] at h1
    simp [φ] at h1
    simp [h1]
  exact not_isHorizontal_of_dimOne h0 hP hs ⟨hW, hrel⟩ hhor

end NoHorizontal

section Integral

theorem ptsIntegral_add_of_dimOne (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [MeasureTheory.integral_unique, MeasureTheory.integral_unique, MeasureTheory.integral_unique,
      ← smul_add]
    congr 1
    have hfin : ∀ y, (fibre P hΨ.choose y).Finite := hFF K ι P 0 hΨ.choose hP hΨ.choose_spec
    refine Eq.trans ?_ (finsum_mem_add_distrib' ((hfin _).subset Set.inter_subset_left)
      ((hfin _).subset Set.inter_subset_left))
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : ∀ y : Fin 0 → ℂ, hγ.choose y ∈ mcPts P := fun y =>
        (Subsingleton.elim _ y) ▸ hγ.choose_spec.2.self_of_nhds.2.1
      rw [h _ (hz _), add_mul]
    · simp
  · simp

theorem arInt_mul_of_dimOne (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) (Fin.elim0 : Fin 0 → HermLine ι) =
      arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) + arInt P t B (Fin.elim0 : Fin 0 → HermLine ι) := by
  unfold arInt
  refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
  have hs0 := eval_ne_zero_of_dimOne h0 hP hs hz
  have ht0 := eval_ne_zero_of_dimOne h0 hP ht hz
  have hA := A.pos z hz.1
  have hB := B.pos z hz.1
  unfold logNorm
  rw [show (A.tensor B).h z = A.h z * B.h z from rfl, map_mul, map_mul, norm_mul, mul_div_mul_comm]
  exact Real.log_mul (div_ne_zero (norm_ne_zero_iff.mpr hs0) hA.ne')
    (div_ne_zero (norm_ne_zero_iff.mpr ht0) hB.ne')

end Integral

theorem SpecIntHeightFormula.proof (h0 : ArithVarZeroStatement) : SpecIntHeightFormula.Statement := by
  intro K _ ι _ I P A s hP _ hs
  rw [recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityAdditive.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement) : RegularityAdditive.Statement := by
  intro K _ ι _ I P A B s t hP _ _ hs ht
  obtain ⟨_, _, _, hsP⟩ := id hs
  obtain ⟨_, _, _, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 _ hsP htP, arInt_mul_of_dimOne h0 hFF hP hs ht]
  ring

theorem cycR_eq_vertR_of_dimOne (h0 : ArithVarZeroStatement) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) :
    cycR I P (Fin.elim0 : Fin 0 → HermLine ι) s = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityIndependence.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : RegularityIndependence.Statement := by
  intro K _ ι _ I P A s t hP hs ht
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  obtain ⟨b, hb, htb, htP⟩ := id ht
  have hab : b = a := funext fun k => by exact_mod_cast (hb k).symm.trans (ha k)
  subst hab
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hsplit : arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / ‖eval z (map (Int.castRingHom ℂ) t)‖)) +
      arInt P t A (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [hφ]
    refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
    have hs0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP hs hz)
    have ht0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP ht hz)
    have hA := (A.pos z hz.1).ne'
    unfold logNorm
    rw [← Real.log_mul (div_ne_zero hs0 ht0) (div_ne_zero ht0 hA)]
    congr 1
    field_simp
  have hpf := hPF K ι P s t b hP hsa htb hsP htP
  rw [recR_eq, recR_eq, cycR_eq_vertR_of_dimOne h0 I hP hs, cycR_eq_vertR_of_dimOne h0 I hP ht, hsplit]
  linarith

theorem R1.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.R1.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.R1.of_first ⟨RegularityIndependence.proof h0 hFF hPF, RegularityAdditive.proof h0 hFF⟩

end

end GroundTheory.Heights₂.Heights.Inter
