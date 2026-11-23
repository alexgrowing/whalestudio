import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativePreservesPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeAlongLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

namespace GlobalTheory.ThK.ZFinDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem theta_facts {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {Ψ} (hΨ : Ψ ∈ GlobalTheory.ThK.PolData B G.M)
    (h : UA σ G.W.J) : Continuous (fun g => theta om Ψ g h) ∧
      (∀ δ ∈ ratU σ G.V.J, ∀ g, theta om Ψ (δ * g) h = theta om Ψ g h) ∧
      IntegrableOn (fun g => theta om Ψ g h) G.M.dom G.M.μ := by
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hS : Ψ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
    refine (Submodule.span_le.2 ?_ : GlobalTheory.ThK.PolData B G.M ≤ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) hΨ
    rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨hc, hr, -⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP).1 Ψ hS
  obtain ⟨hw, -⟩ := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  refine ⟨hc.comp (Continuous.prodMk continuous_id continuous_const), fun δ hδ g => ?_, (hw Ψ hS).1 h⟩
  simpa using hr δ hδ 1 (one_mem _) g h

theorem norm_le_of_hasDerivAt {f f' : ℝ → ℂ} (hd : ∀ s, HasDerivAt f (f' s) s) (hc : Continuous f') {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : ‖f t‖ ≤ ‖f 0‖ + ∫ s in Set.Icc (-1 : ℝ) 1, ‖f' s‖ := by
  have hI : ∫ s in (0 : ℝ)..t, f' s = f t - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)
  have h1 : ‖f t‖ ≤ ‖f 0‖ + ‖∫ s in (0 : ℝ)..t, f' s‖ := by
    rw [hI]
    calc ‖f t‖ = ‖f 0 + (f t - f 0)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖∫ s in (0 : ℝ)..t, f' s‖ ≤ ∫ s in Set.uIoc 0 t, ‖f' s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc
  have h3 : ∫ s in Set.uIoc 0 t, ‖f' s‖ ≤ ∫ s in Set.Icc (-1 : ℝ) 1, ‖f' s‖ := by
    refine setIntegral_mono_set (hc.norm.integrableOn_Icc) (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    refine Filter.Eventually.of_forall fun s (hs : s ∈ Set.uIoc 0 t) => ?_
    show s ∈ Set.Icc (-1 : ℝ) 1
    rw [Set.mem_uIoc] at hs
    obtain ⟨ht₁, ht₂⟩ := ht
    rw [Set.mem_Icc]
    rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> constructor <;> linarith
  linarith

theorem integrableOn_avg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (u : G → ℂ)
    (hu : ∀ δ ∈ Γ, ∀ g, u (δ * g) = u g) (hc : Continuous u) (hi : IntegrableOn u D μ) (c : ℝ → G)
    (hcc : Continuous c) :
    IntegrableOn (fun g => ∫ s in Set.Icc (-1 : ℝ) 1, ‖u (g * c s)‖) D μ := by
  have hcont : Continuous (fun p : G × ℝ => ‖u (p.1 * c p.2)‖) :=
    (hc.comp (continuous_fst.mul (hcc.comp continuous_snd))).norm
  have hprod : Integrable (fun p : G × ℝ => ‖u (p.1 * c p.2)‖)
      ((μ.restrict D).prod (volume.restrict (Set.Icc (-1 : ℝ) 1))) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun s => ?_, ?_⟩
    · exact (GlobalTheory.integrableOn_fundamentalDomain_mul_right hD (c s) u hu hi).norm
    · have hconst : (fun s => ∫ g, ‖‖u (g * c s)‖‖ ∂(μ.restrict D)) = fun _ => ∫ g in D, ‖u g‖ ∂μ := by
        funext s
        have := GlobalTheory.setIntegral_fundamentalDomain_mul_right hD (c s) (fun g => ((‖u g‖ : ℝ) : ℂ))
          (fun δ hδ g => by simp only [hu δ hδ g])
        rw [integral_complex_ofReal, integral_complex_ofReal] at this
        simp only [norm_norm]
        exact_mod_cast this
      rw [hconst]
      exact integrable_const _
  exact hprod.integral_prod_left

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem dom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V, ∀ h, ∃ b : UA σ G.V.J → ℝ, IntegrableOn b G.M.dom G.M.μ ∧
      ∀ g ∈ G.M.dom, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖theta om Ψ (g * γ (Multiplicative.ofAdd t)) h‖ ≤ b g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT Ψ hΨ γ hγ h
  have hΨ' := GlobalTheory.T.line_derivative_preserves_polynomial F E σ B a a' G X om om' hKP hT Ψ hΨ γ hγ
  obtain ⟨-, -, hi⟩ := theta_facts hKP hT hΨ h
  obtain ⟨hcont', hr', hi'⟩ := theta_facts hKP hT hΨ' h
  obtain ⟨htg, hlc, hsc, ht2⟩ := GlobalTheory.UnipCT.topFacts σ G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V.J
  haveI := hT.geo.hM.haar
  haveI : SigmaCompactSpace (UA σ G.V.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite G.M.μ := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite G.M.μ := inferInstance
  haveI := GlobalTheory.T.unitary_haar_right_invariant F E σ B a G.V (a - G.p) G.p hT.base hT.geo.hV G.M.μ hT.geo.hM.haar
  have hcc : Continuous (fun t : ℝ => γ (Multiplicative.ofAdd t)) := hγ.1.comp continuous_ofAdd
  have hderiv : ∀ g (s : ℝ), HasDerivAt (fun t : ℝ => theta om Ψ (g * γ (Multiplicative.ofAdd t)) h)
      (theta om (derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ) (g * γ (Multiplicative.ofAdd s)) h) s := by
    intro g s
    have h0 := GlobalTheory.T.theta_derivative_along_line F E σ B a a' G X om om' hKP hT Ψ hΨ γ hγ (g * γ (Multiplicative.ofAdd s)) h
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h0)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  refine ⟨fun g => ‖theta om Ψ g h‖ + ∫ s in Set.Icc (-1 : ℝ) 1,
      ‖theta om (derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ) (g * γ (Multiplicative.ofAdd s)) h‖, ?_, ?_⟩
  · exact hi.norm.add (integrableOn_avg hT.geo.hM.dom _ hr' hcont' hi' _ hcc)
  · intro g _ t ht
    have := norm_le_of_hasDerivAt (f := fun t : ℝ => theta om Ψ (g * γ (Multiplicative.ofAdd t)) h) (hderiv g)
      (hcont'.comp (continuous_const.mul hcc)) ht
    simpa using this

end GlobalTheory.ThK.ZFinDom

end
