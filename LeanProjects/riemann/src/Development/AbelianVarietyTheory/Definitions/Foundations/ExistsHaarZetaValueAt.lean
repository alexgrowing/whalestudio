import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE

noncomputable section

namespace GlobalTheory.Eis.Model

open scoped NNReal ENNReal ComplexConjugate
open Filter Topology Set MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

theorem exists_cosetSum_eq_one {G : Type} [Group G] (P Γ : Subgroup G) :
    ∃ ψ : G → ℂ, LeftInv (P ⊓ Γ) ψ ∧ ∀ g, CosetConv P Γ ψ g ∧ cosetSum P Γ ψ g = 1 := by
  classical
  let T : Set G := {x | ∃ p ∈ P ⊓ Γ, p * x = (mk Γ x).out}
  have h : LeftInv (P ⊓ Γ) (indicator T (1 : G → ℂ)) := fun γ hγ x => by
    have e : mk Γ (γ * x) = mk Γ x := mk_mul ⟨γ, hγ.2⟩ x
    have : γ * x ∈ T ↔ x ∈ T :=
      ⟨fun ⟨p, hp, b⟩ => ⟨p * γ, mul_mem hp hγ, by rw [mul_assoc, b, e]⟩,
        fun ⟨p, hp, b⟩ => ⟨p * γ⁻¹, mul_mem hp (inv_mem hγ), by rw [e, ← b]; group⟩⟩
    simp only [indicator, this, Pi.one_apply]
  refine ⟨_, h, fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 (Quotient.out_eq (mk Γ g)).symm
  have h0 : ∀ q ≠ mk (P.subgroupOf Γ) γ, term P Γ (indicator T (1 : G → ℂ)) g q = 0 := fun q =>
    Quotient.inductionOn q fun x hx => (term_mk h g x).trans (indicator_of_notMem (s := T) (fun (⟨p, hp, b⟩ : ∃ p ∈ P ⊓ Γ, p * ((x : G) * g) = (mk Γ (x * g)).out) => hx
      (mk_eq_iff.2 ⟨⟨⟨p, hp.2⟩, hp.1⟩, Subtype.ext (mul_right_cancel (b := g) (by
        rw [mk_mul, ← hγ, ← mul_assoc] at b; exact b))⟩)) _)
  refine ⟨summable_of_ne_finset_zero (s := {mk _ γ}) fun q hq => by rw [h0 q (by simpa using hq), norm_zero], ?_⟩
  rw [cosetSum, tsum_eq_single _ h0, term_mk h]
  exact indicator_of_mem (show (γ : G) * g ∈ T from ⟨1, one_mem _, by rw [one_mul, mk_mul, hγ]⟩) _

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) (m : Measure (GA D V)) [m.IsHaarMeasure]

theorem vol_ne_zero : (((autMeasure V m).real univ : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨NeZero.ne _, measure_ne_top _ _⟩)

theorem exists_family (c : ℂ → ℂ) : ∃ Φ : ℂ → GA D (dblSp V) → ℂ, (∀ s g, eis V (Φ s) g = c s) ∧
    IsZetaFamily V 1 m Φ 1 1 ∧ ∀ s, zeta V 1 m Φ 1 1 s = c s * ((autMeasure V m).real univ : ℝ) ^ 2 := by
  obtain ⟨ψ, h1, h2⟩ := exists_cosetSum_eq_one (siegel V) (GQ (dblSp V))
  have e : ∀ s, eis V (c s • ψ) = fun _ => c s := fun s => funext fun g => by
    rw [eis_smul, Pi.smul_apply, eis, (h2 g).2, smul_eq_mul, mul_one]
  have e' : ∀ z : ℂ, dblIntegrandQ V 1 (fun _ => z) 1 1 = fun _ => z :=
    fun z => funext fun _ => by simp [dblIntegrandQ, dblIntegrand]
  refine ⟨fun s => c s • ψ, fun s g => congrFun (e s) g, ⟨IsEisFamily.smul (Φ := fun _ => ψ)
    (fun _ _ => ⟨h1, fun g => (h2 g).1⟩) c, fun s _ => ?_⟩, fun s => ?_⟩
  · beta_reduce
    rw [e]
    exact ⟨fun _ _ _ => rfl, e' _ ▸ integrable_const _⟩
  · simp only [zeta]
    rw [e, dblInt, e', integral_const, ← univ_prod_univ, measureReal_prod_prod, Complex.real_smul]
    push_cast; ring

theorem exists_zeta_eq (h : ℂ → ℂ) : ∃ Φ, IsZetaFamily V 1 m Φ 1 1 ∧ zeta V 1 m Φ 1 1 = h := by
  obtain ⟨Φ, -, a, b⟩ := exists_family V m fun s => h s / ((autMeasure V m).real univ : ℝ) ^ 2
  exact ⟨Φ, a, funext fun s => (b s).trans (div_mul_cancel₀ _ (pow_ne_zero 2 (vol_ne_zero V m)))⟩

theorem exists_zetaValueAt (s₀ z : ℂ) : ∃ Φ, ZetaContinues V 1 m Φ 1 1 ∧ ZetaValueAt V 1 m Φ 1 1 s₀ z ∧
    ZetaCoeffAt V 1 m Φ 1 1 s₀ (-1) 1 ∧ (∀ c, ¬ ZetaHolValueAt V 1 m Φ 1 1 s₀ c) ∧
    ∀ c ≠ z, ¬ ZetaValueAt V 1 m Φ 1 1 s₀ c := by
  obtain ⟨Φ, a, b⟩ := exists_zeta_eq V m fun s => (s - s₀)⁻¹ + z
  have h3 : IsMerExt (zeta V 1 m Φ 1 1) univ fun s => (s - s₀)⁻¹ + z :=
    by rw [b]; exact isMerExt_self isRightDomain_univ fun s _ => by fun_prop
  have h4 : Tendsto (fun s => (s - s₀) ^ 1 * ((s - s₀)⁻¹ + z)) (𝓝[≠] s₀) (𝓝 1) := by
    have : Tendsto (fun s => 1 + (s - s₀) * z) (𝓝[≠] s₀) (𝓝 (1 + (s₀ - s₀) * z)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto (by fun_prop) s₀)
    rw [sub_self, zero_mul, add_zero] at this
    exact this.congr' (eventually_nhdsWithin_of_forall fun s hs => by
      have := sub_ne_zero.2 (show s ≠ s₀ from hs)
      field_simp)
  have h5 : ZetaValueAt V 1 m Φ 1 1 s₀ z := ⟨a, _, h3.isExtAt trivial, Polynomial.X, by simp, by simp⟩
  refine ⟨Φ, ⟨a, _, h3⟩, h5, ⟨a, (h3.isExtAt trivial).coeffAt_of_tendsto h4⟩, fun c h => ?_,
    fun c hc h => hc (h.unique h5)⟩
  have h6 := ((tendsto_nhdsWithin_of_tendsto_nhds (s := {s₀}ᶜ) ((continuous_sub_right s₀).pow 1).continuousAt.tendsto).mul
    ((h3.isExtAt trivial).holValueAt_iff.1 h.2))
  simpa using tendsto_nhds_unique h6 h4

theorem exists_not_zetaValueAt : ∃ Φ, IsZetaFamily V 1 m Φ 1 1 ∧ ∀ s₀ c, ¬ ZetaValueAt V 1 m Φ 1 1 s₀ c := by
  obtain ⟨Φ, a, b⟩ := exists_zeta_eq V m fun s => conj s
  refine ⟨Φ, a, fun s₀ c ⟨_, H, ⟨U, _, ⟨⟨σ, hσ⟩, _⟩, hm, τ, hτ⟩, _⟩ => ?_⟩
  rw [b] at hτ
  have hx : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf (max σ τ) := by simp
  obtain ⟨z, h1, h2⟩ := ((hm _ (hσ (rightOf_subset (le_max_left _ _) hx))).eventually_analyticAt.and
    (mem_nhdsWithin_of_mem_nhds ((isOpen_rightOf _).mem_nhds hx))).exists
  have h3 : DifferentiableAt ℂ (fun s : ℂ => conj s) z := h1.differentiableAt.congr_of_eventuallyEq
    (eventually_of_mem ((isOpen_rightOf _).mem_nhds h2) fun s hs => (hτ (rightOf_subset (le_max_right _ _) hs)).symm)
  have h4 := h3.hasFDerivAt.restrictScalars ℝ
  have h5 := h4.unique (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z))
  have h6 := DFunLike.congr_fun h5 1
  have h7 := DFunLike.congr_fun h5 Complex.I
  have h8 : fderiv ℂ (fun s : ℂ => conj s) z Complex.I = Complex.I * fderiv ℂ (fun s : ℂ => conj s) z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
    Complex.conj_I] at h6 h7
  rw [h6, h7, mul_one] at h8
  exact Complex.I_ne_zero (by linear_combination (-1 / 2 : ℂ) * h8)

omit m in

theorem exists_haar_zetaValueAt (s₀ z : ℂ) : ∃ (m : Measure (GA D V)) (_ : m.IsHaarMeasure) (Φ : ℂ → GA D (dblSp V) → ℂ),
    ZetaValueAt V 1 m Φ 1 1 s₀ z ∧ ∀ c ≠ z, ¬ ZetaValueAt V 1 m Φ 1 1 s₀ c :=
  let ⟨Φ, h⟩ := exists_zetaValueAt V Measure.haar s₀ z
  ⟨Measure.haar, inferInstance, Φ, h.2.1, h.2.2.2.2⟩

omit m in

theorem not_isEisFamily_one [Infinite (GQ V)] : ¬ IsEisFamily V fun _ _ => 1 := fun h => by
  have := Infinite.of_injective _ (injective_mk_io (V := V))
  have h1 := ((h ((V.rank : ℝ) / 2 + 1 : ℝ) (by simp)).2 1).tendsto_cofinite_zero
  simp [term] at h1

end GlobalTheory.Eis.Model

end
