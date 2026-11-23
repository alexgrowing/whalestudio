import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConstOneMemCuspFormsOfAnisotropic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

noncomputable section

open scoped ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.ContModel

theorem hypotheses_inhabited (n b : ℕ) (s₁ : ℂ) :
    ∃ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (φ : GA D (dblSp V) → ℂ),
      V.rank = n ∧ IsMaj V a ∧ HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D μ ∧ ResEta D μ (2 * b) ∧
        φ ∈ degPS V a μ s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  obtain ⟨V, a, -, -, -, -, h1, h2, -⟩ := DblModel.hypotheses_inhabited D n 0
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a h2
  refine ⟨D, V, a, 1, sph V a s₁, h1, h2, hI, ⟨continuous_const, fun _ => rfl⟩, DblModel.resEta_one D b,
    sph_mem hI s₁, fun g => ?_⟩
  rw [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _

variable {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ}

theorem isEisFamily_flat (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    IsEisFamily V (flat V a φ s₁) :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  (sphConv D V a hI).isEisFamily_flat hI hφ hμ

theorem eisCont_right (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    (∀ s ∈ rightOf (V.rank / 2), eisCont V (flat V a φ s₁) s = eis V (flat V a φ s₁ s)) ∧
    (∀ g, DifferentiableOn ℂ (eisCont V (flat V a φ s₁) · g) (rightOf (V.rank / 2))) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V (flat V a φ s₁) x.1 x.2) (rightOf (V.rank / 2) ×ˢ univ) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  have h := isEisFamily_flat ha hμ hφ
  have e : ∀ s ∈ rightOf (V.rank / 2), eisCont V (flat V a φ s₁) s = eis V (flat V a φ s₁ s) := fun s hs =>
    (h.eisValueAt h.analyticOnNhd_flat hs).eisCont_eq
  refine ⟨e, fun g => (h.analyticOnNhd_flat g).differentiableOn.congr fun s hs => congrFun (e s hs) g, ?_⟩
  exact ((sphConv D V a hI).continuousOn_eis hI (continuous_flat hI hφ).continuousOn
    fun s _ => flat_mem hI hφ s).congr fun x hx => congrFun (e _ hx.1) _

theorem one_le_eisCont_sph (ha : IsMaj V a) {σ : ℝ} (hσ : (V.rank : ℝ) / 2 < σ) :
    1 ≤ (eisCont V (flat V a (sph V a σ) σ) σ 1).re := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  rw [(eisCont_right (μ := 1) ha ⟨continuous_const, fun _ => rfl⟩ (sph_mem hI σ)).1 σ (by simpa using hσ)]
  simpa only [flatH_self] using ((sphConv_iff hI).1 (sphConv D V a hI)).2 σ hσ

theorem iff_reduced : Published.SiegelEisensteinContinuation ↔
    ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
      ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
      ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
        (∀ g, Continues (eisSer V (flat V a φ s₁) g)) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k :=
  ⟨fun h D V h0 a ha μ b hμ hb s₁ φ hφ =>
    let h' := h D V h0 a ha (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha) μ b hμ hb s₁ φ hφ
    ⟨h'.1.2, h'.2⟩,
  fun h D V h0 a ha _ μ b hμ hb s₁ φ hφ =>
    let h' := h D V h0 a ha μ b hμ hb s₁ φ hφ
    ⟨⟨isEisFamily_flat ha hμ hφ, h'.1⟩, h'.2⟩⟩

theorem modGrowth_eis (hP : Published.SiegelEisensteinContinuation) (h0 : 0 < V.rank) (ha : IsMaj V a) {b : ℕ}
    (hμ : IsHeckeChar D μ) (hb : ResEta D μ b) (hφ : φ ∈ degPS V a μ s₁) (hs : (V.rank : ℝ) / 2 < s₁.re) :
    Grow.ModGrowth (dblSp V) (eis V φ) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  obtain ⟨k, hk⟩ := (hP D V h0 a ha hI μ b hμ hb s₁ φ hφ).2 s₁
  have hv := (sphConv D V a hI).eisValueAt_flat hI hφ hμ hs
  obtain ⟨r, hr, -, -, C, N, h⟩ := hk.of_eisValueAt hv
  exact ⟨C, N, fun g => hv.eisCont_eq ▸ h s₁ (mem_ball_self hr) g⟩

theorem exists_not_eisContinues (V : HSp D) : ∃ Φ, IsEisFamily V Φ ∧
    (∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf 0)) ∧ ¬ EisContinues V Φ := by
  obtain ⟨Φ, h1, h2, -⟩ := Model.exists_family V Measure.haar fun s => Complex.exp s⁻¹
  have e : ∀ g, eisSer V Φ g = fun s => Complex.exp s⁻¹ := fun g => funext fun s => h1 s g
  have hA : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp s⁻¹) (rightOf 0) := fun s hs =>
    (analyticAt_id.inv (by rintro (rfl : s = 0); simp at hs)).cexp
  refine ⟨Φ, h2.1, fun g => e g ▸ hA, fun h => ?_⟩
  have h3 : (0 : ℂ) ∈ contDom fun s : ℂ => Complex.exp s⁻¹ := by
    rw [(continues_iff hA).1 (e 1 ▸ h.2 1)]; trivial
  obtain ⟨k, hk⟩ := meromorphicOn_cont _ 0 h3
  have hl : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto' 0 0 rfl).comp tendsto_inv_atTop_zero
  have h4 := (hk.continuousAt.tendsto.comp hl).norm
  have h5 : Tendsto (fun t : ℝ => Real.exp t / t ^ k) atTop atTop := Real.tendsto_exp_div_pow_atTop k
  refine not_tendsto_atTop_of_tendsto_nhds h4 (h5.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h6 := eqOn_cont hA (x := ((t⁻¹ : ℝ) : ℂ)) (by simpa using ht)
  simp only [Function.comp, h6, sub_zero, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp]
  simp [abs_of_pos ht, div_eq_inv_mul]

end GlobalTheory.Eis.ContModel

end
