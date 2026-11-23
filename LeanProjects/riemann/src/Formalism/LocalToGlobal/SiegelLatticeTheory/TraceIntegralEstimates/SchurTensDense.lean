import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.LimitMemLpAndIntegralEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensSpan

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

def coeff (σs : K → (Hs →L[ℂ] Hs)) (a b : Hs) (x : K) : ℂ := ⟪b, σs x a⟫_ℂ

theorem continuous_coeff (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (a b : Hs) :
    Continuous (coeff σs a b) := by
  show Continuous fun x => ⟪b, σs x a⟫_ℂ
  exact continuous_const.inner (hstr a)

theorem norm_sq_of_mul_conj (z : ℂ) : ‖z * conj z‖ = ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_conj, sq]

private theorem integrable_norm_sq_coeff_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    Integrable (fun x => ‖coeff σs a b x‖ ^ 2) m := by
  obtain ⟨hi, -⟩ := h
  exact hi.norm.congr (ae_of_all _ fun x => norm_sq_of_mul_conj (coeff σs a b x))

private theorem lintegral_enorm_sq_coeff_eq_ofReal_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (∫ x, ‖coeff σs a b x‖ ^ 2 ∂m) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_coeff_of_SP h)
    (ae_of_all _ fun x => sq_nonneg _)]
  exact lintegral_congr fun x => enorm_sq_eq _

theorem memLp_of_diag (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) {a b : Hs} (h : SP m σs D a b a b) :
    MemLp (coeff σs a b) 2 m :=
  memLp_two_of_lintegral (continuous_coeff hstr a b).aestronglyMeasurable
    (by rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h]; exact ENNReal.ofReal_lt_top)

private theorem mul_conj_eq_ofReal_norm_sq_complex (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem integral_norm_sq_coeff_eq_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫ x, ‖coeff σs a b x‖ ^ 2 ∂m = ‖a‖ ^ 2 * ‖b‖ ^ 2 / D := by
  obtain ⟨-, h2⟩ := h
  have e1 : (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => ((‖coeff σs a b x‖ ^ 2 : ℝ) : ℂ) :=
    funext fun x => mul_conj_eq_ofReal_norm_sq_complex _
  rw [e1] at h2
  rw [integral_complex_ofReal] at h2
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((∫ x, ‖coeff σs a b x‖ ^ 2 ∂m : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖b‖ ^ 2 / D : ℝ) : ℂ) := by
    rw [h2]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3

theorem lintegral_of_diag (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) {a b : Hs} (h : SP m σs D a b a b) :
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (‖a‖ ^ 2 * ‖b‖ ^ 2 / D) := by
  rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h, integral_norm_sq_coeff_eq_of_SP h]

theorem coeff_sub_a (a₁ a₂ b : Hs) : (fun x => coeff σs a₁ b x - coeff σs a₂ b x) = coeff σs (a₁ - a₂) b := by
  funext x
  simp only [coeff, map_sub, inner_sub_right]

theorem coeff_sub_b (a b₁ b₂ : Hs) : (fun x => coeff σs a b₁ x - coeff σs a b₂ x) = coeff σs a (b₁ - b₂) := by
  funext x
  simp only [coeff, inner_sub_left]

theorem small_of_close (c : ℝ) (hc : 0 ≤ c) (hD : 0 < D) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ENNReal.ofReal (t ^ 2 * c / D) ≤ ε := by
  rcases eq_or_ne ε ⊤ with hte | hne
  · exact ⟨1, one_pos, fun _ _ _ => by rw [hte]; exact le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hne
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  refine ⟨min 1 (ε.toReal * D / (c + 1)), lt_min one_pos (div_pos (mul_pos he hD) hc1),
    fun t ht0 htδ => ?_⟩
  rw [← ENNReal.ofReal_toReal hne]
  apply ENNReal.ofReal_le_ofReal
  have h1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have h2 : t < ε.toReal * D / (c + 1) := lt_of_lt_of_le htδ (min_le_right _ _)
  have h4 : t * (c + 1) ≤ ε.toReal * D := by
    have h5 : t * (c + 1) < ε.toReal * D / (c + 1) * (c + 1) := mul_lt_mul_of_pos_right h2 hc1
    rw [div_mul_cancel₀ _ hc1.ne'] at h5
    exact h5.le
  have h3 : t ^ 2 ≤ t := by nlinarith
  have h6 : t ^ 2 * c ≤ t * c := mul_le_mul_of_nonneg_right h3 hc
  have h7 : t ^ 2 * c ≤ ε.toReal * D := by nlinarith
  have h8 : t ^ 2 * c / D ≤ ε.toReal * D / D := by
    exact div_le_div_of_nonneg_right h7 hD.le
  rwa [mul_div_cancel_right₀ _ hD.ne'] at h8

theorem SP_of_dense_a (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (b a' b' : Hs) (hA : ∀ a₀ ∈ Sp, SP m σs D a₀ b a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D c b c b) (hg : MemLp (coeff σs a' b') 2 m) (a : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.1 (hdense a)
  have hf2 : ∀ n, MemLp (coeff σs (u n) b) 2 m := fun n =>
    memLp_of_diag hstr (hdiag _ (hu_mem n))
  have hFm : AEStronglyMeasurable (coeff σs a b) m :=
    (continuous_coeff hstr a b).aestronglyMeasurable
  have hpt : ∀ x, Tendsto (fun n => coeff σs (u n) b x) atTop (𝓝 (coeff σs a b x)) := by
    intro x
    have hσ : Tendsto (fun n => σs x (u n)) atTop (𝓝 (σs x a)) := ((σs x).continuous.tendsto a).comp hu
    show Tendsto (fun n => ⟪b, σs x (u n)⟫_ℂ) atTop (𝓝 ⟪b, σs x a⟫_ℂ)
    exact tendsto_const_nhds.inner hσ
  have hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      ∫⁻ x, ‖coeff σs (u k) b x - coeff σs (u n) b x‖ₑ ^ 2 ∂m ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := small_of_close (‖b‖ ^ 2) (sq_nonneg _) hD ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq δ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsub : ∀ x, coeff σs (u k) b x - coeff σs (u n) b x =
        coeff σs (u k - u n) b x := fun x => congrFun (coeff_sub_a (σs := σs) (u k) (u n) b) x
    calc ∫⁻ x, ‖coeff σs (u k) b x - coeff σs (u n) b x‖ₑ ^ 2 ∂m
        = ∫⁻ x, ‖coeff σs (u k - u n) b x‖ₑ ^ 2 ∂m := by simp only [hsub]
      _ = ENNReal.ofReal (‖u k - u n‖ ^ 2 * ‖b‖ ^ 2 / D) :=
          lintegral_of_diag hstr (hdiag _ (Sp.sub_mem (hu_mem k) (hu_mem n)))
      _ ≤ ε := hsmall _ (norm_nonneg _) (by rw [← dist_eq_norm]; exact hN k hk n hn)
  have hL : Tendsto (fun n => ∫ x, coeff σs (u n) b x * conj (coeff σs a' b' x) ∂m) atTop
      (𝓝 (⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ))) := by
    have e : (fun n => ∫ x, coeff σs (u n) b x * conj (coeff σs a' b' x) ∂m) =
        fun n => ⟪a', u n⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ) := by
      funext n
      obtain ⟨-, he⟩ := hA _ (hu_mem n)
      exact he
    rw [e]
    have hin : Tendsto (fun n => ⟪a', u n⟫_ℂ) atTop (𝓝 ⟪a', a⟫_ℂ) := by
      exact tendsto_const_nhds.inner hu
    exact (hin.mul_const _).div_const _
  obtain ⟨hM, hI, hE⟩ := limit_memLp_and_integral_eq (fun n => coeff σs (u n) b)
    (coeff σs a b) (coeff σs a' b') hf2 hFm hg hpt hC hL
  exact ⟨And.intro hI hE, hM⟩

theorem SP_of_dense_b (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (a a' b' : Hs) (hB : ∀ b₀ ∈ Sp, SP m σs D a b₀ a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D a c a c) (hg : MemLp (coeff σs a' b') 2 m) (b : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.1 (hdense b)
  have hf2 : ∀ n, MemLp (coeff σs a (u n)) 2 m := fun n =>
    memLp_of_diag hstr (hdiag _ (hu_mem n))
  have hFm : AEStronglyMeasurable (coeff σs a b) m :=
    (continuous_coeff hstr a b).aestronglyMeasurable
  have hpt : ∀ x, Tendsto (fun n => coeff σs a (u n) x) atTop (𝓝 (coeff σs a b x)) := by
    intro x
    show Tendsto (fun n => ⟪u n, σs x a⟫_ℂ) atTop (𝓝 ⟪b, σs x a⟫_ℂ)
    exact hu.inner tendsto_const_nhds
  have hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := small_of_close (‖a‖ ^ 2) (sq_nonneg _) hD ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq δ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsub : ∀ x, coeff σs a (u k) x - coeff σs a (u n) x =
        coeff σs a (u k - u n) x := fun x => congrFun (coeff_sub_b (σs := σs) a (u k) (u n)) x
    calc ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m
        = ∫⁻ x, ‖coeff σs a (u k - u n) x‖ₑ ^ 2 ∂m := by simp only [hsub]
      _ = ENNReal.ofReal (‖u k - u n‖ ^ 2 * ‖a‖ ^ 2 / D) := by
          rw [lintegral_of_diag hstr (hdiag _ (Sp.sub_mem (hu_mem k) (hu_mem n))),
            mul_comm (‖a‖ ^ 2)]
      _ ≤ ε := hsmall _ (norm_nonneg _) (by rw [← dist_eq_norm]; exact hN k hk n hn)
  have hL : Tendsto (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) atTop
      (𝓝 (⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ))) := by
    have e : (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) =
        fun n => ⟪a', a⟫_ℂ * ⟪u n, b'⟫_ℂ / (D : ℂ) := by
      funext n
      obtain ⟨-, he⟩ := hB _ (hu_mem n)
      exact he
    rw [e]
    have hin : Tendsto (fun n => ⟪u n, b'⟫_ℂ) atTop (𝓝 ⟪b, b'⟫_ℂ) := by
      exact hu.inner tendsto_const_nhds
    exact (hin.const_mul _).div_const _
  obtain ⟨hM, hI, hE⟩ := limit_memLp_and_integral_eq (fun n => coeff σs a (u n))
    (coeff σs a b) (coeff σs a' b') hf2 hFm hg hpt hC hL
  exact ⟨And.intro hI hE, hM⟩

theorem isSchur_of_dense (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (hSp : ∀ a ∈ Sp, ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, SP m σs D a b a' b') :
    IsSchur m σs D := by

  have h1 : ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, ∀ a : Hs,
      SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b hb a' ha' b' hb' a
    exact SP_of_dense_a hstr hD Sp hdense b a' b' (fun a₀ h₀ => hSp a₀ h₀ b hb a' ha' b' hb')
      (fun c hc => hSp c hc b hb c hc b hb)
      (memLp_of_diag hstr (hSp a' ha' b' hb' a' ha' b' hb')) a

  have h2 : ∀ b ∈ Sp, ∀ b' ∈ Sp, ∀ a a' : Hs, SP m σs D a b a' b' := by
    intro b hb b' hb' a a'
    have h := SP_of_dense_a hstr hD Sp hdense b' a b
      (fun a₀ h₀ => SP_swap (h1 b hb a₀ h₀ b' hb' a).1)
      (fun c hc => hSp c hc b' hb' c hc b' hb')
      (h1 b hb b' hb' b' hb' a).2 a'
    exact SP_swap h.1

  have h3 : ∀ b' ∈ Sp, ∀ a a' b : Hs, SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b' hb' a a' b
    exact SP_of_dense_b hstr hD Sp hdense a a' b'
      (fun b₀ h₀ => h2 b₀ h₀ b' hb' a a')
      (fun c hc => h2 c hc c hc a a)
      (h1 b' hb' b' hb' b' hb' a').2 b

  refine ⟨hD, fun a b a' b' => ?_⟩
  have h4 := SP_of_dense_b hstr hD Sp hdense a' a b
    (fun b₀ h₀ => SP_swap (h3 b₀ h₀ a a' b).1)
    (fun c hc => h2 c hc c hc a' a')
    (h3 0 Sp.zero_mem a a b).2 b'
  exact SP_swap h4.1

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs' : Type} [NormedAddCommGroup Hs'] [InnerProductSpace ℂ Hs']
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs' : (∀ v, G v) → (Hs' →L[ℂ] Hs')} {tens : (∀ v, H v) → Hs'}

theorem isSchur_tens [OpensMeasurableSpace (∀ v, G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    (d : ι → ℝ) (hσ : ∀ v, IsUnitRep (σ v)) (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs' tens) :
    IsSchur (Measure.pi μ) σs' (∏ v, d v) := by
  have hU := isUnitRep_tens hσ h
  obtain ⟨-, -, -, hcont⟩ := hU
  have hh := h
  obtain ⟨-, -, hdense⟩ := hh
  have hD : 0 < ∏ v, d v := Finset.prod_pos fun v _ => by
    obtain ⟨hd, -⟩ := hS v
    exact hd
  have hE : ∀ a ∈ Set.range tens, ∀ b ∈ Set.range tens, ∀ a' ∈ Set.range tens, ∀ b' ∈ Set.range tens,
      SP (Measure.pi μ) σs' (∏ v, d v) a b a' b' := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩ _ ⟨α', rfl⟩ _ ⟨β', rfl⟩
    exact SP_pure μ d hS h α β α' β'
  exact isSchur_of_dense hcont hD (Submodule.span ℂ (Set.range tens)) hdense
    (SP_span hE)

end Tens

end Formalism.L2.S.Pv.SchurTens
