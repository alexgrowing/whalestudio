import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff

noncomputable section

open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def UBnd {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ i, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖f i (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

structure UFam {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  left : ∀ i, IsLeftInvariant (f i)
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ i (g : AdelicGLn.AdelicGL K n) (u : U),
      f i (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = f i g

abbrev mat (y : archGroup K n) : ArchMatrix K n := ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)

structure Ker [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ) : Prop where
  cont : Continuous β
  cpt : HasCompactSupport β
  nonneg : ∀ y, 0 ≤ β y
  mass : ∫ y, β y ∂ν = 1
  lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ y y', |β y - β y'| ≤ L * ‖mat y - mat y'‖

def sm [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ y, (β y : ℂ) * f (x * infEmb K n y) ∂ν

theorem continuous_mat : Continuous (mat : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_ball {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
  have hemb : IsEmbedding (fun y : archGroup K n => mat y) :=
    Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)
  have hsub : Metric.closedBall (1 : ArchMatrix K n) ρ ⊆ Set.range (fun y : archGroup K n => mat y) := by
    intro a ha
    have h1 : ‖1 - a‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using ha) hρ
    refine ⟨⟨Units.oneSub (1 - a) h1, Subgroup.mem_top _⟩, ?_⟩
    simp [mat]
  have := (hemb.isInducing.isCompact_preimage_iff hsub).2 (isCompact_closedBall (1 : ArchMatrix K n) ρ)
  convert this using 1
  ext y
  simp [dist_eq_norm]

theorem tent_lip {A : Type*} [SeminormedAddCommGroup A] {ρ : ℝ} (hρ0 : 0 < ρ) (a b e : A) :
    |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ ρ⁻¹ * ‖a - b‖ := by
  have h1 : |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ |(1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ)| := by
    simp only [max_comm (0 : ℝ)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ) = ρ⁻¹ * (‖b - e‖ - ‖a - e‖) := by
    field_simp
    ring
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hρ0)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ0.le))
  have h3 := abs_norm_sub_norm_le (b - e) (a - e)
  rw [sub_sub_sub_cancel_right] at h3
  rw [norm_sub_rev a b]
  exact h3

theorem exists_ker [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {U : Set (archGroup K n)} (hU : U ∈ 𝓝 1) :
    ∃ β, Ker ν β ∧ tsupport β ⊆ U := by
  have hc : ContinuousAt (fun y : archGroup K n => mat y) 1 := continuous_mat.continuousAt

  have hb : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} ⊆ U := by
    have hemb : IsInducing (fun y : archGroup K n => mat y) :=
      (Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)).isInducing
    rw [hemb.nhds_eq_comap, mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    have h1 : mat (1 : archGroup K n) = 1 := rfl
    rw [h1] at ht
    obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
    refine ⟨min e (1 / 2), by positivity, by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun y hy => hsub ?_⟩
    apply hball
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hy (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hρU⟩ := hb
  set β₀ : archGroup K n → ℝ := fun y => max 0 (1 - ‖mat y - 1‖ / ρ) with hβ₀
  have hβc : Continuous β₀ :=
    continuous_const.max (continuous_const.sub ((continuous_mat.sub continuous_const).norm.div_const _))
  have hsupp : Function.support β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
    intro y hy
    by_contra h
    apply hy
    have h' : ρ < ‖mat y - 1‖ := not_le.1 h
    have : 1 < ‖mat y - 1‖ / ρ := (one_lt_div hρ0).2 h'
    exact max_eq_left (by linarith)
  have hclosed : IsClosed {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} :=
    isClosed_le (continuous_mat.sub continuous_const).norm continuous_const
  have hts : tsupport β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := closure_minimal hsupp hclosed
  have hcs : HasCompactSupport β₀ := (isCompact_ball hρ1).of_isClosed_subset (isClosed_tsupport _) hts
  have hnn : ∀ y, 0 ≤ β₀ y := fun y => le_max_left _ _
  have hpos : 0 < ∫ y, β₀ y ∂ν := by
    refine hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (x := 1) ?_
    have : β₀ 1 = 1 := by simp [hβ₀, mat]
    rw [this]; exact one_ne_zero
  set c := ∫ y, β₀ y ∂ν with hcdef
  have hcpos : 0 ≤ c⁻¹ := inv_nonneg.2 hpos.le
  have hk : Ker ν (fun y => c⁻¹ * β₀ y) := by
    refine { cont := continuous_const.mul hβc
             cpt := hcs.mul_left
             nonneg := fun y => mul_nonneg hcpos (hnn y)
             mass := ?_
             lip := ⟨c⁻¹ * ρ⁻¹, mul_nonneg hcpos (inv_nonneg.2 hρ0.le), fun y y' => ?_⟩ }
    · rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hpos.ne']
    · rw [← mul_sub, abs_mul, abs_of_nonneg hcpos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcpos
      exact tent_lip hρ0 _ _ _
  exact ⟨_, hk, (tsupport_mul_subset_right (f := fun _ => c⁻¹) (g := β₀)).trans (hts.trans hρU)⟩

end GlobalTheory.CompanionTheory.Conc

end
