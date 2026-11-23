import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeEx

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.fin [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    ∫⁻ k, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ∂μK < ⊤ := by
  set J : Fin m → (AE F E)ˣ × UA σ X₁.J → ℂ := fun i x =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) (Ψ i))) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) with hJ
  have hJi : ∀ i, Integrable (J i) (μ.prod (M₀.μ.restrict M₀.dom)) := fun i => h.int _ (hΨ i) h₁
  have key : ∀ k : K, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ≤
      ∑ i, ‖c i k‖ₑ * ∫⁻ x, ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) := fun k => by
    have e1 : ∀ l g, theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
        ∑ i, c i k * J i (l, g) := fun l g => by
      simp only [hd, h.val_sum _ hΨ, hJ, Finset.sum_mul, mul_assoc]
    simp only [e1]
    have hi : Integrable (fun x => ∑ i, c i k * J i x) (μ.prod (M₀.μ.restrict M₀.dom)) :=
      integrable_finset_sum _ fun i _ => (hJi i).const_mul _
    rw [← lintegral_prod (fun x => ‖∑ i, c i k * J i x‖ₑ) hi.1.enorm]
    calc _ ≤ ∫⁻ x, ∑ i, ‖c i k‖ₑ * ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) :=
          lintegral_mono fun x => (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (enorm_mul _ _).le)
      _ = _ := by
          rw [lintegral_finset_sum' _ fun i _ => (hJi i).1.enorm.const_mul _]
          exact Finset.sum_congr rfl fun i _ => lintegral_const_mul'' _ (hJi i).1.enorm
  refine (lintegral_mono key).trans_lt ?_
  rw [lintegral_finset_sum' _ fun i _ => (hc i).1.enorm.mul_const _]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_mul_const'' _ (hc i).1.enorm]
  exact ENNReal.mul_lt_top (hc i).2 (hJi i).2

theorem LineOK.unf [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (ι : (AE F E)ˣ → (AE F E)ˣ)
    (hι : ∀ G : (AE F E)ˣ → ℝ≥0∞, ∫⁻ l, G (ι l) ∂μ = ∫⁻ l, G l ∂μ) (hι' : ∀ G : (AE F E)ˣ → ℂ, ∫ l, G (ι l) ∂μ = ∫ l, G l ∂μ)
    (lev : (AE F E)ˣ × UA σ X₁.J → UA σ X.J) (f : UA σ X.J → ℂ)
    (hf : ∀ l g (k : K), f (lev (ι l, g) * k.1) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g 1 * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) :
    ∫⁻ k, ∫⁻ l, (∫⁻ g in M₀.dom, ‖f (lev (l, g) * k.1)‖ₑ ∂M₀.μ) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ ∂μK < ⊤ ∧
    ∫ k, ∫ l, (∫ g in M₀.dom, f (lev (l, g) * k.1) ∂M₀.μ) * (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) ∂μ ∂μK =
      coneI B M om M₀ om₀ e K μK μ u ν z Φ 1 := by
  constructor
  · convert h.fin μK hΨ hc hd 1 using 3 with k
    rw [← hι]
    congr 1
    funext l
    simp only [← hf, enorm_mul]
    rw [lintegral_mul_const' _ _ (by simp)]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  · unfold coneI
    congr 1
    funext k
    rw [← hι']
    congr 1
    funext l
    simp only [Model.I, mul_assoc, ← integral_mul_const, hf]

end Core

end PositivityTheory.ThKCT

end
