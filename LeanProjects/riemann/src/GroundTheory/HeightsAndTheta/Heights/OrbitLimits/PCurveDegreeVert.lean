import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveDegreeVert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def fsLine (b : K → ℕ) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (b k : ℤ))

theorem isSmoothHerm_fsLine (b : K → ℕ) : IsSmoothHerm (fsLine b : HermLine ι) := by
  have hfun : (fsLine b : HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ b k := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow (b k)
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem sum_eq_of_transversal {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by
  refine Finset.sum_bij (fun t ht => (hR'u t (hRP t ht)).exists.choose)
    (fun t ht => (hR'u t (hRP t ht)).exists.choose_spec.1) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have e1 := (hR'u t₁ (hRP t₁ h₁)).exists.choose_spec.2
    have e2 := (hR'u t₂ (hRP t₂ h₂)).exists.choose_spec.2
    rw [he] at e1
    exact (hRu t₂ (hRP t₂ h₂)).unique ⟨h₁, sameOrbit_trans e2 (sameOrbit_symm e1)⟩ ⟨h₂, sameOrbit_refl t₂⟩
  · intro t' ht'
    obtain ⟨t, ⟨htR, hto⟩, -⟩ := hRu t' (hR'P t' ht')
    exact ⟨t, htR, (hR'u t (hRP t htR)).unique (hR'u t (hRP t htR)).exists.choose_spec
      ⟨ht', sameOrbit_symm hto⟩⟩
  · intro t ht
    exact hh _ _ (hRP t ht) (hR'u t (hRP t ht)).exists.choose_spec.2

theorem logNorm_sameOrbit {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    logNorm A s z = logNorm A s z' := by
  obtain ⟨c, hc, rfl⟩ := h
  unfold logNorm
  have hn : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ a k‖ := by
    simp [ha, norm_prod, norm_pow]
  have h0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog s a hs c z', A.smul c z' hc, norm_mul, hn, mul_div_mul_left _ _ h0]

omit [∀ k, Fintype (ι k)] in
theorem norm_eval_curveChartMono (c : ∀ k, ι k) (e : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (curveChartMono c e))‖ = ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
  simp [curveChartMono, map_prod, norm_prod]

theorem proof : CurveDegreeVert.Statement := by
  intro K _ ι _ P A II c R b d hII hP hA hc hRP hRu hd
  have hI := hII K ι
  have hpr : P.IsPrime := hP.2.1.1
  have hL : ∀ j, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine ι) j) := fun j => j.elim0
  have hsnoc : ∀ C : HermLine ι,
      (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) C : Fin (0 + 1) → HermLine ι) = fun _ => C :=
    fun C => funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  have hmono : ∀ e : K → ℕ, curveChartMono c e ∉ P := by
    intro e h
    rw [curveChartMono, hpr.prod_mem_iff] at h
    obtain ⟨k, _, hk⟩ := h
    exact hc k (hpr.mem_of_pow_mem _ hk)
  set B : HermLine ι := fsLine b with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_fsLine b
  have hBa : ∀ k, B.a k = b k := fun k => rfl
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    show A.a k + B.a k = d k
    rw [hBa, hd k]
  have hsd : IsSectionOn P (A.tensor B) (curveChartMono c d) :=
    ⟨d, hABa, isMultiHomog_curveChartMono c d, hmono d⟩
  have hsb : IsSectionOn P B (curveChartMono c b) := ⟨b, hBa, isMultiHomog_curveChartMono c b, hmono b⟩

  have hnz : ∀ z ∈ mcPts P, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k
    have hs1 : IsSectionOn P (fsLine (fun _ => 1) : HermLine ι) (curveChartMono c fun _ => 1) :=
      ⟨fun _ => 1, fun _ => rfl, isMultiHomog_curveChartMono c _, hmono _⟩
    have h1 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne arithVarZero hP hs1 hz)
    rw [norm_eval_curveChartMono] at h1
    have h2 := Finset.prod_ne_zero_iff.mp h1 k (Finset.mem_univ k)
    simpa using h2

  have hadd := hI.2.1 P 0 Fin.elim0 A B hP hL hA hB
  have hRd := hI.2.2 P 0 Fin.elim0 (A.tensor B) (curveChartMono c d) d hP hL
    (hA.mul hB) hABa (isMultiHomog_curveChartMono c d) (hmono d)
  have hRb := hI.2.2 P 0 Fin.elim0 B (curveChartMono c b) b hP hL hB hBa
    (isMultiHomog_curveChartMono c b) (hmono b)
  rw [hsnoc, hsnoc, hsnoc] at hadd
  rw [hsnoc] at hRd hRb
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsd] at hRd
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsb] at hRb

  obtain ⟨R', hR'P, hR'u, hsum⟩ := regularityPointsSum_holds.proof K ι P hP
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hint : ∀ (C : HermLine ι) (s : MRing ι) (e : K → ℕ), (∀ k, C.a k = e k) → IsMultiHomog s e →
      arInt P s C (Fin.elim0 : Fin 0 → HermLine ι) = ∑ t ∈ R, logNorm C s t := by
    intro C s e hCe hse
    have hinv : ∀ z z', z ∈ mcPts P → SameOrbit z z' → logNorm C s z = logNorm C s z' :=
      fun z z' _ h => logNorm_sameOrbit hCe hse h
    rw [arInt, hφ, hsum _ hinv]
    exact (sum_eq_of_transversal hRP hRu hR'P hR'u _ hinv).symm
  rw [hint _ _ d hABa (isMultiHomog_curveChartMono c d)] at hRd
  rw [hint _ _ b hBa (isMultiHomog_curveChartMono c b)] at hRb

  have hpt : ∀ t ∈ R, logNorm B (curveChartMono c b) t - logNorm (A.tensor B) (curveChartMono c d) t =
      Real.log (chartRadius A c t) := by
    intro t ht
    have hz := hRP t ht
    have hk := hnz t hz
    have hApos := A.pos t hz.1
    have hBpos := B.pos t hz.1
    have hpos : ∀ e : K → ℕ, 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ e k := fun e =>
      Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hk k)) _
    have hsplit : ∏ k, ‖t ⟨k, c k⟩‖ ^ d k =
        (∏ k, ‖t ⟨k, c k⟩‖ ^ b k) * ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (norm_ne_zero_iff.mpr (hk k)), hd k, add_comm]
    unfold logNorm chartRadius
    rw [norm_eval_curveChartMono, norm_eval_curveChartMono, show (A.tensor B).h t = A.h t * B.h t from rfl,
      ← Real.log_div (div_pos (hpos b) hBpos).ne' (div_pos (hpos d) (mul_pos hApos hBpos)).ne', hsplit]
    congr 1
    have := hpos b
    have hq : 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hk k)) _
    field_simp
  rw [← Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  linarith

end CurveDegreeVert

end

end GroundTheory.Heights₂.Heights.Targets
