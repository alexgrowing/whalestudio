import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.HCCusp
open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.Lift ComplexConjugate

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem cont_bdd (hθ : IsInfFam θ) (φ : Mc θ V) :
    Continuous (φ : GA D V → ℂ) ∧ ∃ C : ℝ, ∀ g, ‖(φ : GA D V → ℂ) g‖ ≤ C :=
  ⟨(mem_Mc_iff.1 φ.2).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩

theorem integrableOn_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (hfin : μ 𝓕 ≠ ⊤)
    (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    IntegrableOn (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) 𝓕 μ := by
  obtain ⟨c1, B1, h1⟩ := cont_bdd hθ φ
  obtain ⟨c2, B2, h2⟩ := cont_bdd hθ ψ
  have hc : Continuous (fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g)) :=
    c1.mul (Complex.continuous_conj.comp c2)
  refine Measure.integrableOn_of_bounded (M := B1 * B2) hfin hc.measurable.aestronglyMeasurable (.of_forall fun g => ?_)
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (h1 g) (h2 g) (norm_nonneg _) ((norm_nonneg _).trans (h1 g))

theorem setIntegral_der_mul_conj {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ ψ : Mc θ V) :
    ∫ g in 𝓕, (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g) ∂μ =
      -∫ g in 𝓕, (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) ∂μ := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hH : μ.IsHaarMeasure := inferInstance
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 ⟨hH, h𝓕⟩).2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hH).1
  obtain ⟨c0, B0, b0⟩ := cont_bdd hθ φ
  obtain ⟨c1, B1, b1⟩ := cont_bdd hθ ψ
  obtain ⟨c2, B2, b2⟩ := cont_bdd hθ (der hθ τ hX φ)
  obtain ⟨c3, B3, b3⟩ := cont_bdd hθ (der hθ τ hX ψ)
  have cc : ∀ {f : GA D V → ℂ}, Continuous f → Continuous fun g => conj (f g) :=
    fun h => Complex.continuous_conj.comp h
  have nn : ∀ {f : GA D V → ℂ} {B : ℝ}, (∀ g, ‖f g‖ ≤ B) → 0 ≤ B :=
    fun h => (norm_nonneg _).trans (h 1)
  have sm : ∀ (f : Mc θ V) (g : GA D V), HasDerivAt (fun t : ℝ => (f : GA D V → ℂ) (g * oneP θ V τ X t))
      (Rder θ V τ X f.1 g) 0 := fun f g => hasDerivAt_Rder (mem_Mc_iff.1 f.2).1.smooth hX g
  have key := GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
    (Φ := fun g => (φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g))
    (Φ' := fun g => (der hθ τ hX φ : GA D V → ℂ) g * conj ((ψ : GA D V → ℂ) g) +
      (φ : GA D V → ℂ) g * conj ((der hθ τ hX ψ : GA D V → ℂ) g))
    (B := B0 * B1) (B' := B2 * B1 + B0 * B3)
    (fun γ hγ g => by
      simp only [(mem_Mc_iff.1 φ.2).1.left γ hγ g, (mem_Mc_iff.1 ψ.2).1.left γ hγ g])
    (c0.mul (cc c1)) ((c2.mul (cc c1)).add (c0.mul (cc c3)))
    (fun g => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (b0 g) (b1 g) (norm_nonneg _) (nn b0))
    (fun g => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b2 g) (b1 g) (norm_nonneg _) (nn b2)
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (b0 g) (b3 g) (norm_nonneg _) (nn b0))
    (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    (fun g t => (hasDerivAt_oneP hθ hX (sm φ) g t).mul (hasDerivAt_oneP hθ hX (sm ψ) g t).star)
  rw [integral_add (integrableOn_mul_conj hfin hθ _ _) (integrableOn_mul_conj hfin hθ _ _)] at key
  exact eq_neg_of_add_eq_zero_right key

theorem inner_eq_petersson {μ : Measure (GA D V)} [μ.IsHaarMeasure] (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = petersson V μ ψ.1 φ.1 :=
  petersson_inner_eq_integral_quotient _ hθ ψ φ

theorem inner_eq_setIntegral {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hθ : IsInfFam θ) (φ ψ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ ψ⟫_ℂ = ∫ g in 𝓕, (ψ : GA D V → ℂ) g * conj ((φ : GA D V → ℂ) g) ∂μ := by
  rw [inner_eq_petersson]
  exact petersson_eq h𝓕 (mem_Mc_iff.1 ψ.2).1.left (mem_Mc_iff.1 φ.2).1.left

theorem inner_io_der_skew : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (ψ χ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX ψ), GlobalTheory.CompanionTheory.HCCusp.io μ hθ χ⟫_ℂ = -⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ ψ, GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX χ)⟫_ℂ := by
  intro D θ hθ V μ _ τ X hX ψ χ
  obtain ⟨𝓕, h𝓕⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ inferInstance).2
  rw [inner_eq_setIntegral h𝓕, inner_eq_setIntegral h𝓕]
  exact setIntegral_der_mul_conj h𝓕 hθ τ hX χ ψ

end GlobalTheory.CompanionTheory.HCCusp
end
