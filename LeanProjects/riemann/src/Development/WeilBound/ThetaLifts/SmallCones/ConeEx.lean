import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeBasic

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_prod {α β : Type} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α]
    [BorelSpace β] [SecondCountableTopology α] [SecondCountableTopology β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {θ : α × β → ℂ} (hθ : Continuous θ) {w : α → ℂ} (hw : Continuous w) {a : α → ℝ} (ha : ∀ l, ‖w l‖ = a l)
    (hfin : ∫⁻ l, (∫⁻ g, ‖θ (l, g)‖ₑ ∂ν) * ENNReal.ofReal (a l) ∂μ < ⊤) : Integrable (fun x => θ x * w x.1) (μ.prod ν) := by
  have hc : Continuous fun x : α × β => θ x * w x.1 := hθ.mul (hw.comp continuous_fst)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hc.measurable.enorm.aemeasurable]
  convert hfin using 3 with l
  simp only [enorm_mul]
  rw [lintegral_mul_const' _ _ (by simp), ← ha, ofReal_norm_eq_enorm]

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure LineOK (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (M₀ : Model σ X₁ W₁) (om₀ : Rep σ X₁ W₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Ten F E n d) (ν : Chr F E) (z : ℕ)
    (S : Submodule ℂ (Fn F n d)) : Prop where
  le : ∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)
  stab : ∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S
  sch : ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u l) Ψ) ∈ schA F (Fin n₁ × Fin d₁)
  th : ∀ g h, ∃ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), ∀ Φ ∈ schA F _, l Φ = theta om₀ Φ g h
  int : ∀ Ψ ∈ S, ∀ h₁, Integrable (fun x : (AE F E)ˣ × UA σ X₁.J =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z)) (μ.prod (M₀.μ.restrict M₀.dom))
  lam : ∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
    Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
    l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.theta_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n₁ d₁}
    (hΨ : ∀ i, Ψ i ∈ schA F (Fin n₁ × Fin d₁)) (g h₁) : theta om₀ (∑ i, c i • Ψ i) g h₁ = ∑ i, c i * theta om₀ (Ψ i) g h₁ := by
  obtain ⟨l, -, hl⟩ := h.th g h₁
  rw [← hl _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hl _ (hΨ i), smul_eq_mul]

theorem LineOK.val_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n d} (hΨ : ∀ i, Ψ i ∈ S)
    (l g h₁) : theta om₀ (e (M.co.rho B.ψ (u l) (∑ i, c i • Ψ i))) g h₁ =
      ∑ i, c i * theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ := by
  rw [rho_linear, map_sum]
  simp only [map_smul]
  exact h.theta_sum c (fun i => h.sch l _ (h.le _ (hΨ i))) g h₁

theorem LineOK.coneI_eq [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    coneI B M om M₀ om₀ e K μK μ u ν z Φ h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z Φ) h₁ := by
  choose Λ hΛ hΛ' using fun i => h.lam (Ψ i) (h.le _ (hΨ i))
  have h1 : cone B M om e K μK μ u ν z Φ = ∑ i, (∫ k, c i k ∂μK) • Λ i := by
    funext y
    have e1 : ∀ k : K, ∫ l, e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
        ∑ i, c i k * Λ i y := fun k => by
      have e2 := fun i => hΛ' i _ (ev_adm y)
      simp only [LinearMap.proj_apply] at e2
      simp only [hd, rho_linear, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [integral_finset_sum _ fun i _ => by simpa only [mul_assoc] using (e2 i).1.const_mul (c i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(e2 i).2, ← integral_const_mul]
      simp only [mul_assoc]
    simp only [cone, e1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ fun i _ => (hc i).mul_const _]
    simp only [integral_mul_const]
  have h2 : ∀ i g, theta om₀ (Λ i) g h₁ =
      ∫ l, theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ := fun i g => by
    obtain ⟨l, hl, hl'⟩ := h.th g h₁
    rw [← hl' _ (hΛ i), (hΛ' i l hl).2]
    simp only [hl' _ (h.sch _ _ (h.le _ (hΨ i))), mul_assoc]
  have h3 : ∀ i, IntegrableOn (fun g => theta om₀ (Λ i) g h₁) M₀.dom M₀.μ := fun i => by
    simp only [h2]
    exact (h.int _ (hΨ i) h₁).integral_prod_right
  set T : Fin m → ℂ := fun i => M₀.I om₀ (Λ i) h₁ with hT
  have h4 : ∀ i, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ = T i := fun i => by
    simp only [hT, Model.I, h2]
    rw [← integral_integral_swap (h.int _ (hΨ i) h₁)]
    simp only [integral_mul_const]
  have h5 : ∀ i, Integrable (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) μ :=
    fun i => by
      have := (h.int _ (hΨ i) h₁).integral_prod_left
      simpa only [integral_mul_const, Model.I] using this
  have h6 : ∀ k : K, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) h₁ * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
      ∑ i, c i k * T i := fun k => by
    rw [← Finset.sum_congr rfl fun i _ => congrArg (c i k * ·) (h4 i)]
    simp only [← integral_const_mul]
    rw [← integral_finset_sum _ fun i _ => (h5 i).const_mul _]
    refine integral_congr_ae ?_
    have : ∀ᵐ l ∂μ, ∀ i, Integrable (fun g => theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ *
        ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) (M₀.μ.restrict M₀.dom) :=
      ae_all_iff.2 fun i => (h.int _ (hΨ i) h₁).prod_right_ae
    filter_upwards [this] with l hl
    simp only [Model.I, hd, h.val_sum _ hΨ, mul_assoc, ← integral_mul_const, ← integral_const_mul, Finset.sum_mul]
    rw [integral_finset_sum _ fun i _ => (hl i).const_mul _]
  rw [h1]
  simp only [coneI, h6]
  rw [integral_finset_sum _ fun i _ => (hc i).mul_const _]
  simp only [integral_mul_const, Model.I, h.theta_sum _ hΛ]
  rw [integral_finset_sum _ fun i _ => (h3 i).const_mul _]
  simp only [integral_const_mul, hT, Model.I]

end Core

end PositivityTheory.ThKCT

end
