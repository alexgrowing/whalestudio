import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.idemOp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
      ∀ (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ χ : G → ℂ, IsLocallyConstant χ → (∀ x, ‖χ x‖ = 1) →
      (∀ x ∈ J, ∀ y ∈ J, χ (x * y) = χ x * χ y) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
        ∃ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 ∧ IsIntegralOp μ π ((J : Set G).indicator fun x => (χ x)⁻¹) B ∧
          (∀ v, ∀ x ∈ J, π x (B v) = χ x • B v) ∧ ∀ v, (∀ x ∈ J, π x v = χ x • v) → B v = m • v := by
  intro G _ _ _ _ _ _ μ hμ J hJo hJc χ hχ hn hm V _ _ π hπ
  classical
  set f : G → ℂ := (J : Set G).indicator fun x => (χ x)⁻¹ with hfdef
  have hne : ∀ x, χ x ≠ 0 := fun x h => by simpa [h] using hn x
  have hJcl : IsClopen (J : Set G) := ⟨hJc.isClosed, hJo⟩
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h1 := (IsLocallyConstant.iff_eventually_eq χ).1 hχ x
    by_cases hx : x ∈ (J : Set G)
    · filter_upwards [h1, hJo.mem_nhds hx] with y hy hyJ
      simp only [hfdef, Set.indicator_of_mem hx, Set.indicator_of_mem hyJ, hy]
    · filter_upwards [hJcl.isClosed.isOpen_compl.mem_nhds hx] with y hyJ
      simp only [hfdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem hyJ]
  have hc : HasCompactSupport f :=
    HasCompactSupport.intro hJc fun x hx => Set.indicator_of_notMem hx _
  have hB : IsIntegralOp μ π f (GlobalTheory.OpTrace.smoothOp π μ f) := by
    intro v l
    have hi := hπ.smoothOp_integrand hf hc v
    refine ⟨?_, ?_⟩
    · have := GlobalTheory.OpTrace.integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using this
    · rw [hπ.map_smoothOp (μ := μ) hf hc l v]
      simp only [smul_eq_mul]
  generalize GlobalTheory.OpTrace.smoothOp π μ f = B at hB
  refine ⟨B, (μ.real (J : Set G) : ℂ), ?_, hB, ?_, ?_⟩
  · have h0 : μ (J : Set G) ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
    have h1 : μ (J : Set G) ≠ ⊤ := hJc.measure_lt_top.ne
    have : μ.real (J : Set G) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨h0, h1⟩
    exact_mod_cast this
  · intro v x hx
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hB v (l ∘ₗ π x)).2
    have h2 := (hB v l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ x * (f g * l (π g v))) x]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have e : χ x * f (x * g) = f g := by
      by_cases hg : g ∈ J
      · have hxg : x * g ∈ (J : Set G) := J.mul_mem hx hg
        have hg' : g ∈ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_mem hxg, Set.indicator_of_mem hg', hm x hx g hg]
        have := hne x
        have := hne g
        field_simp
      · have hxg : x * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hx).1 h)
        have hg' : g ∉ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_notMem hxg, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, e, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  · intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, map_smul, sub_eq_zero, (hB v l).2]
    have e : (fun g => f g * l (π g v)) = (J : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · simp only [hfdef, Set.indicator_of_mem hg, hv g hg, map_smul, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (hne g), one_mul]
      · simp only [hfdef, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator_const _ hJo.measurableSet]
    simp
