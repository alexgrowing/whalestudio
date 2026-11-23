import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TransDeriv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem descend_eq_sec {X : Type} {f : G → X} (h : LeftInv Γ f) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) :
    descend Γ f q = f (sec Γ q) := by
  conv_lhs => rw [← mk_sec q]
  exact h.descend_mk _

theorem sec_mul_eq {X : Type} {f : G → X} (h : LeftInv Γ f) (g : G) :
    (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => f (sec Γ q * g)) = descend Γ f ∘ rmul Γ g := by
  funext q
  have e : rmul Γ g q = mk Γ (sec Γ q * g) := by
    conv_lhs => rw [← mk_sec q]
    rfl
  rw [Function.comp_apply, e, h.descend_mk]

variable [μ.IsMulLeftInvariant]

theorem inner_toL2_eq_integral {f : G → ℂ} (hf : MemL2Quotient Γ μ f) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    ⟪u, hf.toL2⟫_ℂ = ∫ q : GlobalTheory.AutomorphicL2Unitary.Quot Γ, conj (u q) * f (sec Γ q) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL2] with q e
  rw [e, descend_eq_sec hf.1]
  simp [mul_comm]

theorem sub_eq_integral {φ ψ : G → ℂ} {c : ℝ → G} (hψ : Continuous ψ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (x : G) (t : ℝ) :
    φ (x * c t) - φ x = ∫ s in (0 : ℝ)..t, ψ (x * c s) := by
  have hs : ∀ s, HasDerivAt (fun r => φ (x * c r)) (ψ (x * c s)) s := fun s => by
    have h2 : HasDerivAt (fun t => φ (x * c s * c t)) (ψ (x * c s)) (s - s) := by simpa using hd (x * c s)
    have h3 := h2.comp_sub_const s s
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have : c r = c s * c (r - s) := by rw [← hadd]; congr 1; ring
    simp only [this, mul_assoc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hs s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [h0]

theorem integrable_pair [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] {ψ : G → ℂ}
    (hψ : MemL2Quotient Γ μ ψ) (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  have hsec := (measurableEmbedding_sec (Γ := Γ)).measurable
  have hm : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => ψ (sec Γ p.2 * c p.1)) :=
    hψc.measurable.comp ((hsec.comp measurable_snd).mul (hc.measurable.comp measurable_fst))
  have hu : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u p.2)) :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) :=
    hu.mul hm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF.enorm.aemeasurable]
  set C : ENNReal := eLpNorm u 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) with hC
  have hb : ∀ s, ∫⁻ q, ‖Function.uncurry (fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) (s, q)‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤ C := fun s => by
    have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (q := 2) (r := 1)
      (Lp.aestronglyMeasurable u) (((hψ.mul_right (c s)).2).1) (fun a b => conj a * b) 1
      (Filter.Eventually.of_forall fun q => by simp)
    have h2 : eLpNorm (descend Γ fun x => ψ (x * c s)) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) = eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
      have e : descend Γ (fun x => ψ (x * c s)) = descend Γ ψ ∘ rmul Γ (c s) := by
        funext q
        rw [descend_eq_sec (hψ.1.mul_right (c s)), ← sec_mul_eq hψ.1]
      rw [e]
      exact eLpNorm_comp_measurePreserving hψ.2.1 (measurePreserving_rmul (c s))
    rw [eLpNorm_one_eq_lintegral_enorm, h2] at h1
    simp only [ENNReal.coe_one, one_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun q => ?_
    simp only [Function.uncurry, descend_eq_sec (hψ.1.mul_right (c s))]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (Lp.memLp u).2 hψ.2.2) ?_
  simp [Set.uIoc, Real.volume_Ioc]

variable [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem R_sub_eq_integral {φ ψ : G → ℂ} (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (t : ℝ) :
    R Γ μ (c t) hφ.toL2 - hφ.toL2 = ∫ s in (0 : ℝ)..t, R Γ μ (c s) hψ.toL2 := by
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  refine ext_inner_left ℂ fun u => ?_
  have e1 := (innerSL ℂ u).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply] at e1
  rw [← e1, inner_sub_right]
  simp only [right_translate_toL2, inner_toL2_eq_integral]
  have hi : ∀ {f : G → ℂ} (hf : MemL2Quotient Γ μ f),
      Integrable (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u q) * f (sec Γ q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := fun {f} hf => by
    have h := (Lp.memLp u).star.integrable_mul hf.2
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [descend_eq_sec hf.1]
  rw [← integral_sub (hi (hφ.mul_right (c t))) (hi hφ), intervalIntegral.intervalIntegral_eq_integral_uIoc,
    integral_integral_swap (integrable_pair hψ hψc hc u t), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [integral_const_mul]
  rw [← mul_sub, sub_eq_integral hψc hc h0 hadd hd, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [mul_smul_comm]

theorem hasDerivAt_R : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c _ hψc hc h0 hadd hd t
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  have e : (fun s => R Γ μ (c s) hφ.toL2) = fun s => hφ.toL2 + ∫ r in (0 : ℝ)..s, R Γ μ (c r) hψ.toL2 := by
    funext s
    rw [← R_sub_eq_integral hφ hψ hψc hc h0 hadd hd s]
    abel
  rw [e]
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

end GlobalTheory.CompanionTheory.TransDeriv
