import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary

theorem enorm_sub_sq_le {c f : ℝ → ℂ} (hf : Continuous f) (hd : ∀ t, HasDerivAt c (f t) t) :
    ‖c 1 - c 0‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
  have e : c 1 - c 0 = ∫ t in (0 : ℝ)..1, f t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable _ _)).symm
  have n1 : ‖c 1 - c 0‖ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ := by
    rw [e]
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hn : Continuous fun t => ‖f t‖ := hf.norm
  set A := ∫ t in (0 : ℝ)..1, ‖f t‖ with hA
  set B := ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 with hB
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hAB : A ^ 2 ≤ B := by
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
    have h1 : (∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2) = B - 2 * A * A + A ^ 2 := by
      have : ∀ t, (‖f t‖ - A) ^ 2 = ‖f t‖ ^ 2 - 2 * A * ‖f t‖ + A ^ 2 := fun t => by ring
      simp only [this]
      have i1 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1 := (hn.pow 2).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun t => 2 * A * ‖f t‖) volume 0 1 :=
        (continuous_const.mul hn).intervalIntegrable _ _
      rw [intervalIntegral.integral_add (f := fun t => ‖f t‖ ^ 2 - 2 * A * ‖f t‖) (g := fun _ => A ^ 2) (i1.sub i2)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
      simp [← hA, ← hB]
    nlinarith
  have hle : ‖c 1 - c 0‖ ^ 2 ≤ B := (pow_le_pow_left₀ (norm_nonneg _) n1 2).trans hAB
  have hBi : B = ∫ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ ^ 2 := intervalIntegral.integral_of_le zero_le_one
  have hint : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    ((hn.pow 2).intervalIntegrable 0 1).1
  have hL : ENNReal.ofReal B = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
    rw [hBi, ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  rw [← hL, ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {φ ψ : G → ℂ}

theorem ofReal_norm_sq (h : MemL2Quotient Γ μ φ) :
    ENNReal.ofReal (‖h.toL2‖ ^ 2) = ∫⁻ g in stdDom Γ, ‖φ g‖ₑ ^ (2 : ℝ) ∂μ := by
  have hE : eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := h.2.2.ne
  have h1 : ‖h.toL2‖ = (eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ)).toReal := Lp.norm_toLp _ _
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := descend Γ φ) (μ := AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (by norm_num)
  have h3 := lintegral_quotMeasure (isFundamentalDomain_stdDom Γ μ) (fun q => ‖descend Γ φ q‖ₑ ^ (2 : ℝ))
  simp only [h.1.descend_mk] at h3
  rw [← h3, h1, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE]
  simpa using h2

theorem memL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : MemL2Quotient Γ μ fun x => φ x - ψ x := by
  have hd := isFundamentalDomain_stdDom Γ μ
  exact (memL2_iff_fundamental_domain hd).2 ⟨fun γ hγ g => by simp only [h.1 γ hγ, h'.1 γ hγ], ((memL2_iff_fundamental_domain hd).1 h).2.sub ((memL2_iff_fundamental_domain hd).1 h').2⟩

theorem toL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : (memL2_sub h h').toL2 = h.toL2 - h'.toL2 := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e1 := (memL2_sub h h').lift_toL2_ae_eq
  have e2 : lift Γ (h.toL2 - h'.toL2) =ᵐ[μ] lift Γ h.toL2 - lift Γ h'.toL2 :=
    ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 h'.toL2)
  exact e1.trans ((h.lift_toL2_ae_eq.sub h'.lift_toL2_ae_eq).symm.trans e2.symm)

variable [μ.IsMulRightInvariant]

theorem norm_R_sub_le [SFinite μ] {a : ℝ → G} {u : G} (ha : Continuous a) (h0 : a 0 = 1) (h1 : a 1 = u) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) (hd : ∀ g t, HasDerivAt (fun s => φ (g * a s)) (ψ (g * a t)) t) :
    ‖R Γ μ u hφ.toL2 - hφ.toL2‖ ≤ ‖hψ.toL2‖ := by
  subst h1
  have hm := hφ.mul_right (a 1)
  have hs := memL2_sub hm hφ
  rw [right_translate_toL2, ← toL2_sub hm hφ]
  have key : ∫⁻ g in stdDom Γ, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ := by
    have hpt : ∀ g, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) := fun g => by
      have := enorm_sub_sq_le (c := fun s => φ (g * a s)) (f := fun t => ψ (g * a t)) (by fun_prop) (hd g)
      simpa [h0] using this
    have hmeas : Measurable fun p : G × ℝ => ‖ψ (p.1 * a p.2)‖ₑ ^ (2 : ℝ) :=
      (Continuous.measurable (by fun_prop : Continuous fun p : G × ℝ => ψ (p.1 * a p.2))).enorm.pow_const _
    calc _ ≤ ∫⁻ g in stdDom Γ, (∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ)) ∂μ := lintegral_mono hpt
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) ∂μ) :=
        lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ) := by
        refine lintegral_congr fun t => ?_
        rw [← ofReal_norm_sq (hψ.mul_right (a t)), ← ofReal_norm_sq hψ, ← right_translate_toL2, norm_R]
      _ = _ := by simp
  have h1 := (ofReal_norm_sq hs).le.trans (key.trans (ofReal_norm_sq hψ).ge)
  have h2 : ‖hs.toL2‖ ^ 2 ≤ ‖hψ.toL2‖ ^ 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end Abstract

end GlobalTheory.CompanionTheory.HCCusp.Transl

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.SmoothForms

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem coe_derInf (hθ : IsInfFam θ) (X : LieN V) (φ : Mc θ V) :
    (derInf hθ X φ : GA D V → ℂ) = Der (expInf θ V) X φ.1 := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs : Sm (expInf θ V) φ.1 := (smooth_iff R φ.1).1 (mem_Mc_iff.1 φ.2).1.smooth
  funext g
  have e1 : (derInf hθ X φ : GA D V → ℂ) g = ∑ τ, Rder θ V τ (X τ).1 φ.1 g := by
    simp only [derInf, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun τ _ => rfl
  rw [e1]
  have e2 : ∀ τ, Rder θ V τ (X τ).1 φ.1 g = Der (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ)) φ.1 g := fun τ =>
    congrFun (Rder_eq R τ (X τ) φ.1) g
  have hX : ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V) = X := sum_atPlace X
  rw [Finset.sum_congr rfl fun τ _ => (e2 τ).trans (DerLinear.der_eq_fderiv hs _ g), DerLinear.der_eq_fderiv hs X g]
  exact (map_sum (fderiv ℝ (fun Z : LieN V => φ.1 (g * expInf θ V Z)) 0) (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V))
    Finset.univ).symm.trans (congrArg _ hX)

end GlobalTheory.CompanionTheory.HCCusp.Transl

theorem GlobalTheory.CompanionTheory.HCCusp.norm_Rcusp_expInf_sub_le : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.SmoothForms.LieN V) (φ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ‖GlobalTheory.Cusp.Rcusp V μ (GlobalTheory.SmoothForms.expInf θ V X) (GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ) - GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ‖ ≤ ‖GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ)‖ := by
  intro D θ hθ V μ _ _ X φ
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let a : ℝ → GA D V := fun t => GlobalTheory.SmoothForms.expInf θ V (t • X)
  have ha : Continuous a := (GlobalTheory.CuspGeo.MeanValue.continuous_expInf hθ R).comp (continuous_id.smul continuous_const)
  have h0 : a 0 = 1 := by
    simpa [a] using GlobalTheory.CuspGeo.MeanValue.expInf_zero R
  have h1 : a 1 = GlobalTheory.SmoothForms.expInf θ V X := by simp [a]
  have hP := GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound
  have hφc := (GlobalTheory.Cusp.mem_cuspForms.1 φ.2).1
  set ψ := GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ with hψdef
  have hψf := (GlobalTheory.Cusp.mem_cuspForms.1 ψ.2).1
  have hs : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ V) φ.1 :=
    (GlobalTheory.SmoothForms.smooth_iff R φ.1).1 (GlobalTheory.CompanionTheory.HCCusp.mem_Mc_iff.1 φ.2).1.smooth
  have d0 : ∀ h, HasDerivAt (fun t : ℝ => φ.1 (h * a t)) (ψ.1 h) 0 := fun h => by
    rw [hψdef, GlobalTheory.CompanionTheory.HCCusp.Transl.coe_derInf]
    exact DifferentiableAt.hasDerivAt
      ((((hs h).differentiable (by simp)).comp (differentiable_id.smul_const X)) 0)
  have hd : ∀ g t, HasDerivAt (fun s => φ.1 (g * a s)) (ψ.1 (g * a t)) t := fun g t => by
    have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact d0 (g * a t))
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [a, mul_assoc, ← GlobalTheory.CuspGeo.MeanValue.expInf_add R, add_sub_cancel]
  have := GlobalTheory.CompanionTheory.HCCusp.Transl.norm_R_sub_le ha h0 h1 (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hφc)
    (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hψf) hψf.1.cont hd
  exact this

end
