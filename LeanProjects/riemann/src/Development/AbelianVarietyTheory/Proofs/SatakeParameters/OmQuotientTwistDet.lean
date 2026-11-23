import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.OmTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * χ) g h Φ =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        om μ g h Φ := by
  funext x
  simp only [om, MonoidHom.mul_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_inv]
  ring

theorem tmap_twist {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (χ : kˣ →* ℂˣ)
    (g : GL (Fin r) k) (h : GL (Fin n) k) :
    TensorProduct.map (twist σ (detChar (Fin r) χ) g) (twist τ (detChar (Fin n) χ⁻¹) h) =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        TensorProduct.map (σ g) (τ h) := by
  apply TensorProduct.ext'
  intro v w
  simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem omQuot_mul {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (μ χ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
    (hq : OmQuot μ σ τ) :
    OmQuot (μ * χ) (twist σ (detChar (Fin r) χ)) (twist τ (detChar (Fin n) χ⁻¹)) := by
  obtain ⟨f, hf0, hf⟩ := hq
  refine ⟨f, hf0, fun g h Φ Φ' hΦ' => ?_⟩
  set c : ℂˣ := χ (Matrix.GeneralLinearGroup.det g) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ with hc
  let Ψ : SB (Matrix (Fin n) (Fin r) k) := ((c⁻¹ : ℂˣ) : ℂ) • Φ'
  have hΨ : (Ψ : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ := by
    show ((c⁻¹ : ℂˣ) : ℂ) • (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = _
    rw [hΦ', om_mul, ← hc, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hΦΨ : Φ' = (c : ℂ) • Ψ := by
    show Φ' = (c : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • Φ')
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  rw [tmap_twist, ← hc, hΦΨ, map_smul, hf g h Φ Ψ hΨ, LinearMap.smul_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), OmQuot μ σ τ ↔ OmQuot 1 (twist σ (detChar (Fin r) μ⁻¹)) (twist τ (detChar (Fin n) μ)) := by
  intro k _ _ _ _ r n μ V W _ _ _ _ σ τ
  constructor
  · intro hq
    have := omQuot_mul μ μ⁻¹ σ τ hq
    rwa [mul_inv_cancel, inv_inv] at this
  · intro hq
    have := omQuot_mul 1 μ _ _ hq
    have e1 : detChar (Fin r) μ * detChar (Fin r) μ⁻¹ = (1 : GL (Fin r) k →* ℂˣ) := by
      ext g; simp
    have e2 : detChar (Fin n) μ⁻¹ * detChar (Fin n) μ = (1 : GL (Fin n) k →* ℂˣ) := by
      ext g; simp
    rwa [one_mul, twist_twist, twist_twist, e1, e2, twist_one, twist_one] at this

end GlobalTheory.OmTwist
