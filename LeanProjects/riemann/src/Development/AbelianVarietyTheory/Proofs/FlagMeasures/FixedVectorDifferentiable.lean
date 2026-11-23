import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DFactsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed

open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open Filter Topology
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GardingVec

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = w) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasDerivAt (fun s => ρ (e s) w) (∫ y in tsupport a, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) w) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  rw [hform, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact key.2
  · intro y hy
    rw [hzero 0 y (by simpa [he0] using hy), zero_smul]

theorem decay_setIntegral {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) {K : Set G} (hK : IsCompact K) (φ : G → ℂ) (hφ : Continuous φ)
    (d : G → ℝ) (hd : Continuous d) (hsub : ∀ a b, d (a * b) ≤ d a + d b) (c : ℝ) (hc0 : 0 ≤ c) (v : H)
    (h : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g w⟫_ℂ‖ ≤ C * Real.exp (-(c * d g))) :
    ∃ C : ℝ, ∀ g, ‖⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ‖ ≤ C * Real.exp (-(c * d g)) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun y => ‖φ y‖ * Real.exp (c * d y⁻¹))
    (hφ.norm.mul (Real.continuous_exp.comp (continuous_const.mul (hd.comp continuous_inv)))).continuousOn
  have hint : IntegrableOn (fun y => φ y • ρ y w) K μ :=
    (hφ.smul hc).continuousOn.integrableOn_compact hK
  refine ⟨C * M * μ.real K, fun g => ?_⟩
  have e1 : ⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ = ∫ y in K, φ y * ⟪v, ρ (g * y) w⟫_ℂ ∂μ := by
    have := ContinuousLinearMap.integral_comp_comm ((innerSL ℂ v).comp (ρ g)) hint
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul, smul_eq_mul] at this
    simp only [hmul, this]
  rw [e1]
  refine (norm_setIntegral_le_of_norm_le_const (C := C * M * Real.exp (-(c * d g)))
    hK.measure_lt_top fun y hy => ?_).trans (le_of_eq (by ring))
  have h1 : d g ≤ d (g * y) + d y⁻¹ := by simpa using hsub (g * y) y⁻¹
  have h2 : Real.exp (-(c * d (g * y))) ≤ Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have h3 : ‖φ y‖ * Real.exp (c * d y⁻¹) ≤ M := (le_abs_self _).trans (hM y hy)
  rw [norm_mul]
  calc ‖φ y‖ * ‖⟪v, ρ (g * y) w⟫_ℂ‖
      ≤ ‖φ y‖ * (C * (Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)))) :=
        mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
    _ = C * (‖φ y‖ * Real.exp (c * d y⁻¹)) * Real.exp (-(c * d g)) := by ring
    _ ≤ _ := by gcongr

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem tendsto_slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) s) (𝓝[≠] s)
      (𝓝 (NormedSpace.exp ((s : ℂ) • X) * X)) := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((s : ℝ) : ℂ))
  have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((s : ℂ) • X) * X) s := h2.congr_deriv (by rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; rfl)
  exact h3.tendsto_slope

theorem continuous_exp_curve {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end

theorem hasDerivAt_exp_mul {n : ℕ} (X y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    HasDerivAt (F := Fin n → Fin n → ℂ) (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) * y : Matrix _ _ ℂ))
      (NormedSpace.exp ((s : ℂ) • X) * X * y : Matrix _ _ ℂ) s := by
  refine (hasDerivAt_iff_tendsto_slope (F := Fin n → Fin n → ℂ)).mpr ?_
  have h := (tendsto_slope_exp X s).mul_const y
  refine h.congr (fun t => ?_)
  have : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, slope f s t * y = slope (fun t => f t * y) s t := by
    intro f
    simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul]
  exact this _

theorem fixed_vector_differentiable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  intro n ε H _ _ _ σ α w hσ hα hs hw
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let φ : Matrix (Fin n) (Fin n) ℂ → UJ ε → ℂ := fun X y =>
    fderiv ℝ F (umat y) ((-X) * umat y : Matrix _ _ ℂ)
  have hφ : ∀ X, Continuous (φ X) := fun X =>
    (hfd.comp hu).clm_apply (continuous_const.matrix_mul hu)
  have hφi : ∀ X, IntegrableOn (fun y => φ X y • σ (umat y) w)
      (tsupport fun g : UJ ε => α (umat g)) (muG ε) := fun X =>
    ((hφ X).smul hc).continuousOn.integrableOn_compact hs.isCompact
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H :=
    { toFun := fun X => ∫ y in tsupport fun g : UJ ε => α (umat g), φ X y • σ (umat y) w ∂(muG ε)
      map_add' := fun X Y => by
        rw [← integral_add (hφi X) (hφi Y)]
        congr 1; funext y
        rw [← add_smul]
        congr 1
        have : (-(X + Y) * umat y : Matrix _ _ ℂ) = -X * umat y + -Y * umat y := by
          rw [neg_add, Matrix.add_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_add _ _
      map_smul' := fun r X => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext y
        rw [← smul_assoc]
        congr 1
        have : (-(r • X) * umat y : Matrix _ _ ℂ) = r • (-X * umat y) := by
          rw [← smul_neg, Matrix.smul_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_smul _ _ }
  refine ⟨L, fun X hX => ⟨?_, fun c v hc0 h => ?_⟩⟩
  · let e : ℝ → UJ ε := fun t =>
      ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
    have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
      rw [smul_neg, Matrix.exp_neg, ← hev]
      exact Matrix.coe_units_inv _
    have he : Continuous e := by
      rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
      exact continuous_exp_curve X
    have he0 : e 0 = 1 := by
      apply Subtype.ext; apply Units.ext
      show umat (e 0) = 1
      rw [hev]; simp
    have hcE := continuous_exp_curve (-X)
    have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w hmul hc _ ha hs hw' e he he0
      (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
        (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
      ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
        (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
      (fun s y => by
        simp only [hFα']
        simp only [hum, hei]
        exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
          (hasDerivAt_exp_mul (-X) (umat y) s))
    simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
    exact key
  · exact decay_setIntegral (muG ε) (fun g => σ (umat g)) w hmul hc hs.isCompact (φ X) (hφ X)
      (fun g => dOp (umat g)) ((dFacts_holds n ε).2.1.comp_continuous hu hmem)
      (fun a b => ((dFacts_holds n ε).1 _ (hmem a)).2.2.1 _ (hmem b)) c hc0 v h

end GlobalTheory.GardingVec
