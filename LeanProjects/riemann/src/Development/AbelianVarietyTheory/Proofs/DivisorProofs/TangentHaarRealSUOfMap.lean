import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealIndependentSkewMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraSpannedStatement

noncomputable section

namespace GlobalTheory.SUVol.DensOne

open MeasureTheory Filter Topology Matrix Metric Set GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal

variable {E : Type} [Field E] {r : ℕ}

theorem hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem dot_mulVec_star (A P : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) :
    (P *ᵥ u) ⬝ᵥ (A *ᵥ star v) = u ⬝ᵥ ((Pᵀ * A) *ᵥ star v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]

theorem star_mulVec' (P : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    star (P *ᵥ v) = P.map (starRingEnd ℂ) *ᵥ star v := by
  ext a; simp [mulVec, dotProduct]

theorem eq_of_forall_dot (B C : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ u v : Fin r → ℂ, u ⬝ᵥ (B *ᵥ star v) = u ⬝ᵥ (C *ᵥ star v)) : B = C := by
  ext a b
  have := h (Pi.single a 1) (Pi.single b 1)
  have e : star (Pi.single b (1 : ℂ) : Fin r → ℂ) = Pi.single b 1 := by
    ext c; by_cases hc : c = b <;> simp [hc]
  simpa [e] using this

theorem mem_realSU_iff (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (g : Ψ → GL (Fin r) ℂ) :
    g ∈ realSU Ψ G ↔ ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ)ᵀ * G.map τ.1 *
      (g τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = G.map τ.1 ∧
        (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
  change (∀ τ : Ψ, _ ∧ _) ↔ _
  refine forall_congr' fun τ => ?_
  rw [and_comm]
  refine and_congr_left fun _ => ?_
  have key : ∀ u v : Fin r → ℂ, hermC τ.1 G ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ v) = u ⬝ᵥ (((g τ : Matrix (Fin r) (Fin r) ℂ)ᵀ * G.map τ.1 *
        (g τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) *ᵥ star v) := by
    intro u v
    rw [hermC_eq, star_mulVec', mulVec_mulVec, dot_mulVec_star, Matrix.mul_assoc]
  simp only [key, hermC_eq]
  constructor
  · intro h
    exact eq_of_forall_dot _ _ h
  · intro h u v
    rw [h]

theorem mem_realLie_iff (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (X : Ψ → Fin r → Fin r → ℂ) :
    X ∈ realLie Ψ G ↔ ∀ τ : Ψ, (Matrix.of (X τ))ᵀ * G.map τ.1 + G.map τ.1 * (Matrix.of (X τ)).map (starRingEnd ℂ) = 0 ∧
        (Matrix.of (X τ)).trace = 0 := by
  change (∀ τ : Ψ, _ ∧ _) ↔ _
  refine forall_congr' fun τ => ?_
  rw [and_comm]
  refine and_congr_left fun _ => ?_
  simp only [hermC_eq, dot_mulVec_star, star_mulVec', mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  constructor
  · intro h
    exact eq_of_forall_dot _ 0 fun u v => by simpa using h u v
  · intro h u v
    rw [h]; simp

section Chart

variable (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)

theorem det_map_ne (hG : G.det ≠ 0) (τ : E →+* ℂ) : (G.map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero τ).2 hG

theorem exp_mem_realSU (hG : G.det ≠ 0) (X : realLie Ψ G) :
    (fun τ : Ψ => (⟨NormedSpace.exp (Matrix.of (X.1 τ)), NormedSpace.exp (-Matrix.of (X.1 τ)),
      GlobalTheory.UpqExpChart.exp_mul_exp_neg _, GlobalTheory.UpqExpChart.exp_neg_mul_exp _⟩ : GL (Fin r) ℂ)) ∈ realSU Ψ G := by
  rw [mem_realSU_iff]
  intro τ
  have hX := (mem_realLie_iff Ψ G X.1).1 X.2 τ
  refine ⟨?_, ?_⟩
  · have := exp_twist (det_map_ne G hG τ.1) (Matrix.of (X.1 τ))
    rwa [(twist_eq_iff (det_map_ne G hG τ.1) _).2 hX.1] at this
  · change (NormedSpace.exp (Matrix.of (X.1 τ))).det = 1
    rw [det_exp, hX.2, Complex.exp_zero]

def chartExp (hG : G.det ≠ 0) (X : realLie Ψ G) : realSU Ψ G := ⟨_, exp_mem_realSU Ψ G hG X⟩

def matR (g : realSU Ψ G) : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (g.1 τ : GL (Fin r) ℂ)

theorem matR_injective : Function.Injective (matR Ψ G) :=
  fun _ _ h => Subtype.ext (funext fun i => Units.ext (congrFun h i))

theorem continuous_matR : Continuous (matR Ψ G) :=
  continuous_pi fun i => Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)

theorem matR_one : matR Ψ G 1 = 1 := rfl

theorem continuous_chartExp (hG : G.det ≠ 0) : Continuous (chartExp Ψ G hG) := by
  refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val)
  · exact GlobalTheory.UpqExpChart.continuous_matExp.comp ((continuous_apply i).comp continuous_subtype_val).neg

theorem chartExp_zero (hG : G.det ≠ 0) : chartExp Ψ G hG 0 = 1 :=
  matR_injective Ψ G (funext fun i => NormedSpace.exp_zero (𝔸 := Matrix (Fin r) (Fin r) ℂ))

theorem eventually_mem_image (hG : G.det ≠ 0) {U : Set (realLie Ψ G)} (hU : U ∈ 𝓝 0) :
    ∀ᶠ g in Filter.comap (matR Ψ G) (𝓝 1), g ∈ chartExp Ψ G hG '' U := by
  have hH : ∀ τ : Ψ, (G.map τ.1).det ≠ 0 := fun τ => det_map_ne G hG τ.1
  obtain ⟨e, he, h0⟩ := GlobalTheory.UpqExpChart.exists_chart (n := Fin r)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have he0 : e 0 = 1 := by rw [he]; exact NormedSpace.exp_zero
  have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ e.target := he0 ▸ e.map_source h0
  have hs1 : e.symm 1 = 0 := he0 ▸ e.left_inv h0
  have hm : ∀ i, Tendsto (fun g : realSU Ψ G => matR Ψ G g i) (Filter.comap (matR Ψ G) (𝓝 1)) (𝓝 1) :=
    fun i => ((continuous_apply i).tendsto (1 : Ψ → Matrix (Fin r) (Fin r) ℂ)).comp tendsto_comap
  have hZ : ∀ i, Tendsto (fun g : realSU Ψ G => e.symm (matR Ψ G g i)) (Filter.comap (matR Ψ G) (𝓝 1))
      (𝓝 0) := fun i => hs1 ▸ (e.continuousAt_symm h1).tendsto.comp (hm i)
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have a1 : ∀ᶠ g in Filter.comap (matR Ψ G) (𝓝 1), ∀ i, matR Ψ G g i ∈ e.target :=
    eventually_all.2 fun i => hm i (e.open_target.mem_nhds h1)
  have a2 : ∀ᶠ g in Filter.comap (matR Ψ G) (𝓝 1), ∀ i, twist (G.map i.1) (e.symm (matR Ψ G g i)) ∈ e.source :=
    eventually_all.2 fun i => (((continuous_twist (G.map i.1)).tendsto 0).comp (hZ i))
      (e.open_source.mem_nhds (by simpa [twist] using h0))
  have a3 : ∀ᶠ g in Filter.comap (matR Ψ G) (𝓝 1), ∀ i, (e.symm (matR Ψ G g i)).trace ∈ ball (0 : ℂ) 1 :=
    eventually_all.2 fun i => ((continuous_id.matrix_trace.tendsto 0).comp (hZ i))
      (isOpen_ball.mem_nhds (by simp))
  have a4 : ∀ᶠ g in Filter.comap (matR Ψ G) (𝓝 1),
      ((fun i => e.symm (matR Ψ G g i)) : Ψ → Fin r → Fin r → ℂ) ∈ V :=
    (tendsto_pi_nhds.2 hZ) hV
  filter_upwards [a1, a2, a3, a4] with g b1 b2 b3 b4
  have hexp : ∀ i, NormedSpace.exp (e.symm (matR Ψ G g i)) = matR Ψ G g i := fun i => he ▸ e.right_inv (b1 i)
  have hmem : ((fun i => e.symm (matR Ψ G g i)) : Ψ → Fin r → Fin r → ℂ) ∈ realLie Ψ G := by
    refine (mem_realLie_iff Ψ G _).2 fun i => ?_
    have hg := ((mem_realSU_iff Ψ G g.1).1 g.2 i)
    refine ⟨(twist_eq_iff (hH i) _).1 (hinj (b2 i) (e.map_target (b1 i)) (exp_twist_eq (hH i) ?_)), ?_⟩
    · rw [hexp]; exact hg.1
    · change (e.symm (matR Ψ G g i)).trace = 0
      have c1 : Complex.exp (e.symm (matR Ψ G g i)).trace = Complex.exp 0 := by
        rw [← det_exp, hexp, Complex.exp_zero]; exact hg.2
      have c2 := (abs_lt.1 ((Complex.abs_im_le_norm _).trans_lt (mem_ball_zero_iff.1 (b3 i))))
      have := Real.pi_gt_three
      exact Complex.exp_inj_of_neg_pi_lt_of_le_pi (by linarith [c2.1]) (by linarith [c2.2])
        (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]) c1
  exact ⟨⟨_, hmem⟩, hVU b4, matR_injective Ψ G (funext fun i => hexp i)⟩

end Chart

section Density

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)

def incl : realLie Ψ G →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X τ => Matrix.of (X.1 τ), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem norm_incl (X : realLie Ψ G) : ‖incl Ψ G X‖ = ‖X‖ := rfl

theorem incl_injective : Function.Injective (incl Ψ G) := fun _ _ h => Subtype.ext h

theorem hasStrictFDerivAt_chart (hG : G.det ≠ 0) :
    HasStrictFDerivAt (fun X => matR Ψ G (chartExp Ψ G hG X)) (incl Ψ G) 0 := by
  refine hasStrictFDerivAt_pi'' fun i => ?_
  have h1 := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ψ => Matrix (Fin r) (Fin r) ℂ) i).comp
    (incl Ψ G)).hasStrictFDerivAt (x := 0)
  have h2 : HasStrictFDerivAt (𝕜 := ℝ) (NormedSpace.exp : Matrix (Fin r) (Fin r) ℂ → _)
      (ContinuousLinearMap.id ℝ _) (((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Ψ => Matrix (Fin r) (Fin r) ℂ) i).comp (incl Ψ G)) 0) := by
    rw [map_zero]; exact GlobalTheory.CompactDualExists.exp_strict
  exact h2.comp 0 h1

theorem exists_approx (hG : G.det ≠ 0) {κ : ℝ} (hκ : 0 < κ) : ∃ δ > 0, ∀ X : realLie Ψ G, ‖X‖ < δ →
    ‖matR Ψ G (chartExp Ψ G hG X) - 1 - incl Ψ G X‖ ≤ κ * ‖X‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 (hasStrictFDerivAt_chart Ψ G hG).hasFDerivAt).def hκ
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := hh (y := X) (by rwa [dist_zero_right])
  simp only [zero_add, chartExp_zero, matR_one] at this
  calc _ ≤ _ := this
    _ = κ * ‖X‖ := rfl

theorem mem_grpBall_iff {ε : ℝ} (hε : 0 < ε) (g : realSU Ψ G) :
    g ∈ grpBall (realSU Ψ G) ε ↔ ‖matR Ψ G g - 1‖ < ε := by
  rw [pi_norm_lt_iff hε]
  simp only [Matrix.norm_lt_iff hε]
  rfl

theorem preimage_tanBall {ε : ℝ} (hε : 0 < ε) :
    (Subtype.val : realLie Ψ G → _) ⁻¹' tanBall Ψ r ε = ball 0 ε := by
  ext X
  rw [mem_ball_zero_iff, Set.mem_preimage, Submodule.coe_norm, pi_norm_lt_iff hε]
  simp only [pi_norm_lt_iff hε]
  rfl

theorem chart_squeeze (hG : G.det ≠ 0) {t : ℝ} (ht : 1 < t) : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    chartExp Ψ G hG '' ball 0 (t⁻¹ * ε) ⊆ grpBall (realSU Ψ G) ε ∧
      grpBall (realSU Ψ G) ε ⊆ chartExp Ψ G hG '' ball 0 (t * ε) := by
  have ht0 : 0 < t := by linarith
  have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
  obtain ⟨δ1, hδ1, H1⟩ := exists_approx Ψ G hG (κ := t - 1) (by linarith)
  obtain ⟨δ2, hδ2, H2⟩ := exists_approx Ψ G hG (κ := 1 - t⁻¹) (by linarith)
  have hev := eventually_mem_image Ψ G hG (ball_mem_nhds (0 : realLie Ψ G) hδ2)
  rw [Filter.eventually_comap] at hev
  obtain ⟨ρ, hρ, hh⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Ioo_mem_nhdsGT (lt_min (mul_pos ht0 hδ1) hρ)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  rw [lt_min_iff] at hε1
  constructor
  · rintro _ ⟨X, hX, rfl⟩
    rw [mem_ball_zero_iff] at hX
    rw [mem_grpBall_iff Ψ G hε0]
    have hXδ : ‖X‖ < δ1 := by
      calc ‖X‖ < t⁻¹ * ε := hX
        _ < t⁻¹ * (t * δ1) := by gcongr; exact hε1.1
        _ = δ1 := by field_simp
    have h := H1 X hXδ
    have h2 : ‖matR Ψ G (chartExp Ψ G hG X) - 1‖ ≤ ‖incl Ψ G X‖ +
        ‖matR Ψ G (chartExp Ψ G hG X) - 1 - incl Ψ G X‖ := by
      calc _ = ‖incl Ψ G X + (matR Ψ G (chartExp Ψ G hG X) - 1 - incl Ψ G X)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_incl] at h2
    have h3 : t * ‖X‖ < ε := by
      calc t * ‖X‖ < t * (t⁻¹ * ε) := by gcongr
        _ = ε := by field_simp
    nlinarith
  · intro g hg
    rw [mem_grpBall_iff Ψ G hε0] at hg
    obtain ⟨X, hX, rfl⟩ := hh (y := matR Ψ G g) (by rw [dist_eq_norm]; linarith) g rfl
    rw [mem_ball_zero_iff] at hX
    refine ⟨X, ?_, rfl⟩
    rw [mem_ball_zero_iff]
    have h := H2 X hX
    have h2 : ‖incl Ψ G X‖ ≤ ‖matR Ψ G (chartExp Ψ G hG X) - 1‖ +
        ‖matR Ψ G (chartExp Ψ G hG X) - 1 - incl Ψ G X‖ := by
      calc ‖incl Ψ G X‖ = ‖(matR Ψ G (chartExp Ψ G hG X) - 1) -
            (matR Ψ G (chartExp Ψ G hG X) - 1 - incl Ψ G X)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [norm_incl] at h2
    have h3 : t⁻¹ * ‖X‖ < ε := by linarith
    calc ‖X‖ = t * (t⁻¹ * ‖X‖) := by field_simp
      _ < t * ε := by gcongr

theorem tangentHaar_realSU_of_det [NumberField E] [NumberField.IsCMField E] (hG : G.det ≠ 0) [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure] :
    (tangentHaar (realSU Ψ G) (lam.map Subtype.val)).IsHaarMeasure ∧
      HasDensityOne (realSU Ψ G) (tangentHaar (realSU Ψ G) (lam.map Subtype.val)) (lam.map Subtype.val) := by
  let L₀ : (Ψ → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((Ψ → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  obtain ⟨c, hc0, hct, hc⟩ := exists_density_of_immersion (realLie Ψ G) (Ψ → Matrix (Fin r) (Fin r) ℂ)
    (realSU Ψ G) lam Measure.haar (chartExp Ψ G hG) (matR Ψ G) (incl Ψ G) (incl_injective Ψ G)
    (fun g => L₀ (matR Ψ G g)) (continuous_chartExp Ψ G hG) (chartExp_zero Ψ G hG)
    (hasStrictFDerivAt_chart Ψ G hG) (hL₀.comp (continuous_matR Ψ G)).continuousAt
    (by ext1 A; exact one_mul A) (fun g h => rfl)
    (fun ε hε => (tendsto_iff_comap.1 ((continuous_matR Ψ G).tendsto 1))
      (eventually_mem_image Ψ G hG (ball_mem_nhds 0 hε)))
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze
    (F := fun ε => (Measure.haar : Measure (realSU Ψ G)) (chartExp Ψ G hG '' ball 0 ε))
    (V := fun ε => lam (ball 0 ε)) (A := fun ε => (Measure.haar : Measure (realSU Ψ G)) (grpBall (realSU Ψ G) ε))
    (n := Module.finrank ℝ (realLie Ψ G)) hct
    (fun t ε ht _ => Measure.addHaar_ball_mul_of_pos lam 0 ht ε) hc
    (fun t ht => (chart_squeeze Ψ G hG ht).mono fun ε h => ⟨measure_mono h.1, measure_mono h.2⟩)
  have hν : ∀ ε : ℝ, 0 < ε → (lam.map Subtype.val) (tanBall Ψ r ε) = lam (ball 0 ε) := by
    intro ε hε
    rw [Measure.map_apply measurable_subtype_coe, preimage_tanBall Ψ G hε]
    rw [show tanBall Ψ r ε = ball (0 : Ψ → Fin r → Fin r → ℂ) ε by
      ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl]
    exact measurableSet_ball
  have hA : Tendsto (fun ε => (Measure.haar : Measure (realSU Ψ G)) (grpBall (realSU Ψ G) ε) /
      (lam.map Subtype.val) (tanBall Ψ r ε)) (𝓝[>] 0) (𝓝 c) := by
    refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hν ε hε]
  have hlim : limsup (fun ε : ℝ => (lam.map Subtype.val) (tanBall Ψ r ε) /
      (Measure.haar : Measure (realSU Ψ G)) (grpBall (realSU Ψ G) ε)) (𝓝[>] 0) = c⁻¹ := by
    refine Tendsto.limsup_eq ((ENNReal.tendsto_inv_iff.2 hA).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : (0 : ℝ) < ε := hε
    rw [hν ε hε]
    exact ENNReal.inv_div (Or.inl (measure_ball_lt_top).ne) (Or.inl (measure_ball_pos lam 0 hε).ne')
  unfold tangentHaar
  rw [hlim]
  refine ⟨Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hct) (ENNReal.inv_ne_top.2 hc0), ?_⟩
  have := ENNReal.Tendsto.const_mul hA (Or.inr (ENNReal.inv_ne_top.2 hc0)) (a := c⁻¹)
  rw [ENNReal.inv_mul_cancel hc0 hct] at this
  refine this.congr fun ε => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

end Density

section Corollaries

variable (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)

theorem tangentHaar_realSU_of_map [NumberField E] [NumberField.IsCMField E] (hG : G.det ≠ 0)
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Φ : V →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ))
    (hinj : Function.Injective Φ) (hrange : ∀ X, X ∈ realLie Ψ G ↔ ∃ v, Φ v = X) :
    (tangentHaar (realSU Ψ G) (μ.map Φ)).IsHaarMeasure ∧
      HasDensityOne (realSU Ψ G) (tangentHaar (realSU Ψ G) (μ.map Φ)) (μ.map Φ) := by
  let Φ' : V →ₗ[ℝ] realLie Ψ G := Φ.codRestrict (realLie Ψ G) fun v => (hrange _).2 ⟨v, rfl⟩
  have hb : Function.Bijective Φ' := by
    refine ⟨fun v w h => hinj (congrArg Subtype.val h), fun X => ?_⟩
    obtain ⟨v, hv⟩ := (hrange X.1).1 X.2
    exact ⟨v, Subtype.ext hv⟩
  let φ : V ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ' hb).toContinuousLinearEquiv
  have : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  have e : μ.map Φ = (μ.map φ).map Subtype.val := by
    rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
    rfl
  rw [e]
  exact tangentHaar_realSU_of_det Ψ G hG (μ.map φ)

theorem tangentHaar_riemLie [NumberField E] [NumberField.IsCMField E] (hG : G.det ≠ 0) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)] :
    (tangentHaar (realSU Ψ G) (riemLie Ψ G x)).IsHaarMeasure ∧
      HasDensityOne (realSU Ψ G) (tangentHaar (realSU Ψ G) (riemLie Ψ G x)) (riemLie Ψ G x) := by
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective (fromFrame x) := by
    intro Y Z h
    have hτ : ∀ τ, Matrix.of (fun a b => Y (τ, a, b)) = Matrix.of (fun a b => Z (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z (τ, a, b)) * (mat x τ)⁻¹ := congrFun h τ
      rw [← key1 τ (Matrix.of (fun a b => Y (τ, a, b))), h1, key1]
    refine PiLp.ext fun p => ?_
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  have hsurj : ∀ X, ∃ Y, fromFrame x Y = X := by
    intro X
    refine ⟨WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X p.1) * mat x p.1) p.2.1 p.2.2), funext fun τ => ?_⟩
    have e : Matrix.of (fun a b => (WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
        ((mat x p.1)⁻¹ * Matrix.of (X p.1) * mat x p.1) p.2.1 p.2.2) :
          EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)) =
        (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ := by
      ext a b; simp
    change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X τ
    rw [e, key2]
    rfl
  unfold riemLie
  refine tangentHaar_realSU_of_map Ψ G hG
    (stdOrthonormalBasis ℝ ((realLie Ψ G).comap (fromFrame x))).toBasis.addHaar
    ((fromFrame x).comp ((realLie Ψ G).comap (fromFrame x)).subtype) (hinj.comp Subtype.val_injective)
    fun X => ⟨fun hX => ?_, fun ⟨v, hv⟩ => hv ▸ v.2⟩
  obtain ⟨Y, hY⟩ := hsurj X
  exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact hX⟩, hY⟩

end Corollaries

section FormLie

variable (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)

theorem herm_eq [NumberField E] [NumberField.IsCMField E] (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem skew_matrix [NumberField E] [NumberField.IsCMField E] {X : Matrix (Fin r) (Fin r) E}
    (h : ∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) : Xᵀ * G + G * X.map cc = 0 := by
  have hc : ∀ (P : Matrix (Fin r) (Fin r) E) (y : Fin r → E),
      (fun b => cc ((P *ᵥ y) b)) = P.map cc *ᵥ fun b => cc (y b) := by
    intro P y; ext a; simp [mulVec, dotProduct, cc, map_sum, map_mul]
  have key : ∀ u w : Fin r → E, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) =
      u ⬝ᵥ ((Xᵀ * G + G * X.map cc) *ᵥ fun b => cc (w b)) := by
    intro u w
    rw [herm_eq, herm_eq, hc, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec u Xᵀ, vecMul_transpose]
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [key] at h1
  have e : (fun c => cc ((Pi.single b (1 : E) : Fin r → E) c)) = Pi.single b 1 := by
    ext c; by_cases hcb : c = b <;> simp [hcb, cc]
  rw [e] at h1
  simpa [mulVec_single_one, Matrix.mul_assoc] using h1

theorem map_skew [NumberField E] [NumberField.IsCMField E] {X : Matrix (Fin r) (Fin r) E}
    (h : Xᵀ * G + G * X.map cc = 0) (τ : E →+* ℂ) :
    (X.map τ)ᵀ * G.map τ + G.map τ * (X.map τ).map (starRingEnd ℂ) = 0 := by
  have e : (X.map τ).map (starRingEnd ℂ) = (X.map cc).map τ := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add τ (map_add τ), h, Matrix.map_zero _ (map_zero τ)]

def coordMap {n : ℕ} (e : Fin n → Matrix (Fin r) (Fin r) E) :
    (Ψ → Fin n → ℝ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun c τ a b := ∑ i, (c τ i : ℂ) * τ.1 (e i a b)
  map_add' c d := by ext τ a b; simp [add_mul, Finset.sum_add_distrib]
  map_smul' s c := by ext τ a b; simp [Finset.mul_sum, mul_assoc]

theorem coordMap_apply {n : ℕ} (e : Fin n → Matrix (Fin r) (Fin r) E) (c : Ψ → Fin n → ℝ) (τ : Ψ) :
    Matrix.of (coordMap Ψ e c τ) = ∑ i, c τ i • (e i).map τ.1 := by
  ext a b; simp [coordMap, Matrix.sum_apply, Complex.real_smul]

theorem tangentHaar_formLie [NumberField E] [NumberField.IsCMField E] (hG : G.det ≠ 0)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E)
    (he : ∀ i, (e i).trace = 0 ∧ ∀ x y, herm G (e i *ᵥ x) y + herm G x (e i *ᵥ y) = 0)
    (hli : LinearIndependent (NumberField.maximalRealSubfield E) e)
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)] :
    (tangentHaar (realSU Ψ G) (formLie Ψ e)).IsHaarMeasure ∧
      HasDensityOne (realSU Ψ G) (tangentHaar (realSU Ψ G) (formLie Ψ e)) (formLie Ψ e) := by
  have hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0 := fun i => skew_matrix G (he i).2
  have hE : LinearIndependent E e := GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli
  have hR : ∀ τ : Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1) := fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE
  have hmem : ∀ (τ : Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧
      ((e i).map τ.1).trace = 0 := by
    intro τ i
    refine ⟨map_skew G (hsk i) τ.1, ?_⟩
    have h1 : ((e i).map τ.1).trace = τ.1 (e i).trace := by simp [Matrix.trace, map_sum]
    rw [h1, (he i).1, map_zero]
  unfold formLie
  refine tangentHaar_realSU_of_map Ψ G hG volume (coordMap Ψ e) ?_ fun X => ⟨fun hX => ?_, ?_⟩
  · refine (injective_iff_map_eq_zero (coordMap Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_
    have h1 := coordMap_apply Ψ e c τ
    rw [hc] at h1
    exact Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i
  · have hX' := (mem_realLie_iff Ψ G X).1 hX
    have hspan : ∀ τ : Ψ, Matrix.of (X τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1) :=
      fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2
    choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)
    refine ⟨c, funext fun τ => ?_⟩
    have h1 := coordMap_apply Ψ e c τ
    rw [hc τ] at h1
    exact h1
  · rintro ⟨c, rfl⟩
    refine (mem_realLie_iff Ψ G _).2 fun τ => ?_
    rw [coordMap_apply]
    have h1 : (fun _ : Unit => ∑ i, c τ i • (e i).map τ.1) = ∑ i, c τ i • (fun _ : Unit => (e i).map τ.1) := by
      ext u; simp [Finset.sum_apply]
    have hS : (fun _ : Unit => ∑ i, c τ i • (e i).map τ.1) ∈ suLie (fun _ : Unit => G.map τ.1) := by
      rw [h1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ fun _ => hmem τ i
    exact hS ()

end FormLie

end GlobalTheory.SUVol.DensOne
