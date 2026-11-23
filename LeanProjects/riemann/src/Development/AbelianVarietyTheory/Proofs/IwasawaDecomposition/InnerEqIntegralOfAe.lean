import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne

open Formalism.BasicNotions Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem inner_eq_integral_of_ae {α : Type} [MeasurableSpace α] {m : Measure α} (f g : Lp ℂ 2 m) (f' g' : α → ℂ)
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') : ⟪f, g⟫_ℂ = ∫ x, star (f' x) * g' x ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem eq_smul_of_eval {α A E V : Type} [MeasurableSpace α] {m : Measure α} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ (Lp ℂ 2 m)) (φ : E → V → α → ℂ) (p : V → V → ℂ)
    (hS : ∀ T T', ∃ k : ℂ, ∀ v v', ∫ x, star (φ T v x) * φ T' v' x ∂m = k * p v v')
    (v₁ v₀ : V) (hp : p v₁ v₁ = 1) (j' : E ≃ₗ[ℂ] W) (hj' : ∀ T, ((j' T : W) : Lp ℂ 2 m) =ᵐ[m] φ T v₁)
    (e : A → E) (j : A → W) (a : ℂ) (hj : ∀ F, ((j F : W) : Lp ℂ 2 m) =ᵐ[m] fun x => a * φ (e F) v₀ x) (F : A) :
    j F = (a * p v₁ v₀) • j' (e F) := by
  have hmix : ∀ T : E, ⟪j' T, j F⟫_ℂ = (a * p v₁ v₀) * ⟪j' T, j' (e F)⟫_ℂ := by
    intro T
    obtain ⟨k, hk⟩ := hS T (e F)
    have h1 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj F)
    have h2 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj' (e F))
    rw [hk, hp, mul_one] at h2
    have h3 : ∫ x, star (φ T v₁ x) * (a * φ (e F) v₀ x) ∂m = a * ∫ x, star (φ T v₁ x) * φ (e F) v₀ x ∂m := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h3, hk] at h1
    rw [Submodule.coe_inner, Submodule.coe_inner, h1, h2]
    ring
  obtain ⟨T, hT⟩ := j'.surjective (j F - (a * p v₁ v₀) • j' (e F))
  have hz : ⟪j F - (a * p v₁ v₀) • j' (e F), j F - (a * p v₁ v₀) • j' (e F)⟫_ℂ = 0 := by
    conv_lhs => enter [2]; rw [← hT]
    rw [inner_sub_right, inner_smul_right, hmix, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_conj_scalar {A W H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup H]
    [Module ℂ H] (s : W →ₗ⋆[ℂ] H) (j f : A →ₗ[ℂ] W) (hj : Function.Injective j) (β : ℂ) (h : ∀ F, j F = β • f F) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ F, s (f F) = κ • s (j F) := by
  by_cases h0 : β = 0
  · refine ⟨1, one_ne_zero, fun F => ?_⟩
    have hF : j F = 0 := by rw [h, h0, zero_smul]
    have hF0 : F = 0 := hj (hF.trans (map_zero j).symm)
    subst hF0
    simp
  · refine ⟨(starRingEnd ℂ β)⁻¹, inv_ne_zero ((map_ne_zero _).2 h0), fun F => ?_⟩
    rw [h, LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).2 h0), one_smul]

theorem sEEofTT_eq_smul_conjHH : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) → EvalTieT M μ 𝓕 E St G ι t c → ∀ (e : D.what₂.EE →ₗ[ℂ] E) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (v₀ : M.Vec) (a : ℂ), (∀ F, ((j F : EEC St G) : L2X St) =ᵐ[muX St] fun x => a * ev M v₀ (e F : MMap M) (ι.symm x * t)) → ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ F, sEEofTT M μ 𝓕 E St G ι t c (e F) = κ₀ • conjHH St G (j F) := by
  intro D S M E St G μ 𝓕 ι t c hS hT e j v₀ a hj
  have hv := hT.choose_spec.1
  have hj' := fun T => (hT.choose_spec.2.choose_spec T).1
  have hp : ∏ τ, ⟪(hT.choose τ : M.H τ), (hT.choose τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  have hkey := eq_smul_of_eval (m := muX St) (EEC St G) (fun (T : E) (v : M.Vec) x => (T : MMap M) v (ι.symm x * t))
    (fun v v' => ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) (fun T T' => hS T T.2 T' T'.2) hT.choose v₀ hp
    hT.choose_spec.2.choose hj' e j a hj
  have hs : sEEofTT M μ 𝓕 E St G ι t c
      = (conjHH St G).toLinearMap.comp hT.choose_spec.2.choose.toLinearMap := dif_pos hT
  rw [hs]
  exact exists_conj_scalar (conjHH St G).toLinearMap j.toLinearEquiv.toLinearMap
    (hT.choose_spec.2.choose.toLinearMap.comp e) j.injective _ hkey

end GlobalTheory.Mem.SJ
