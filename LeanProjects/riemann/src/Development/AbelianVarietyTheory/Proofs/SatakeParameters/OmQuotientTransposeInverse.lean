import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HoweTranspose

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def trH (a b : ℕ) : Matrix (Fin a) (Fin b) k ≃ₜ Matrix (Fin b) (Fin a) k where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem comp_trH_mem {a b : ℕ} {f : Matrix (Fin b) (Fin a) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin b) (Fin a) k)) : f ∘ trH a b ∈ SB (Matrix (Fin a) (Fin b) k) :=
  ⟨hf.1.comp_continuous (trH a b).continuous, hf.2.comp_homeomorph (trH a b)⟩

def trL (a b : ℕ) : SB (Matrix (Fin b) (Fin a) k) →ₗ[ℂ] SB (Matrix (Fin a) (Fin b) k) where
  toFun Ψ := ⟨Ψ.1 ∘ trH a b, comp_trH_mem Ψ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_trL (a b : ℕ) (Φ : SB (Matrix (Fin a) (Fin b) k)) : trL a b (trL b a Φ) = Φ := by
  apply Subtype.ext
  funext x
  show Φ.1 x.transpose.transpose = Φ.1 x
  rw [Matrix.transpose_transpose]

theorem det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    Matrix.GeneralLinearGroup.det (θ g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hθ, Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv]

theorem nabs_det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det (θ g)) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  rw [det_transInv θ hθ]
  simp [nabs, map_inv]

theorem rpow_inv_half {a : ℝ} (ha : 0 < a) (c : ℝ) : (a⁻¹) ^ (c / 2) = a ^ (-c / 2) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, neg_div]

theorem om_trans {r n : ℕ} (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k)
    (hr : ∀ g, (θr g).val = (g⁻¹).val.transpose) (hn : ∀ g, (θn g).val = (g⁻¹).val.transpose)
    (g : GL (Fin n) k) (h : GL (Fin r) k) (Ψ : Matrix (Fin r) (Fin n) k → ℂ) :
    om 1 g h Ψ ∘ trH n r = om 1 (θr h) (θn g) (Ψ ∘ trH n r) := by
  funext x
  have hm : ((θn g)⁻¹ : GL (Fin n) k).val * x * (θr h).val = (h⁻¹.val * x.transpose * g.val).transpose := by
    rw [← map_inv, hn, hr, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  simp only [om, Function.comp_apply, map_one, MonoidHom.one_apply, Units.val_one, inv_one, one_mul,
    Fintype.card_fin]
  rw [nabs_det_transInv θr hr, nabs_det_transInv θn hn, rpow_inv_half (nabs_pos' k _),
    rpow_inv_half (nabs_pos' k _), neg_neg, hm]
  have e1 : trH n r (h⁻¹.val * x.transpose * g.val).transpose = h⁻¹.val * x.transpose * g.val :=
    Matrix.transpose_transpose _
  have e2 : trH n r x = x.transpose := rfl
  rw [e1, e2]
  ring

end GlobalTheory.HoweTranspose

open GlobalTheory.HoweTranspose in

theorem GlobalTheory.omQuot_transpose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k), (∀ g, (θr g).val = (g⁻¹).val.transpose) → (∀ g, (θn g).val = (g⁻¹).val.transpose) → OmQuot 1 σ τ → OmQuot 1 (τ.comp θn : Representation ℂ (GL (Fin n) k) W) (σ.comp θr : Representation ℂ (GL (Fin r) k) V) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ θr θn hr hn ⟨f, hf0, hf⟩
  refine ⟨(TensorProduct.comm ℂ V W).toLinearMap ∘ₗ f ∘ₗ trL n r, ?_, ?_⟩
  · intro h0
    apply hf0
    ext Φ
    have := LinearMap.congr_fun h0 (trL r n Φ)
    simp only [LinearMap.coe_comp, Function.comp_apply, trL_trL, LinearEquiv.coe_coe,
      LinearMap.zero_apply] at this
    simpa using this
  · intro g h Ψ Ψ' hΨ
    have key : f (trL n r Ψ') = TensorProduct.map (σ (θr h)) (τ (θn g)) (f (trL n r Ψ)) := by
      refine hf (θr h) (θn g) _ _ ?_
      show Ψ'.1 ∘ trH n r = om 1 (θr h) (θn g) (Ψ.1 ∘ trH n r)
      rw [hΨ]
      exact om_trans θr θn hr hn g h Ψ.1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, MonoidHom.coe_comp]
    exact (TensorProduct.map_comm _ _ _).symm
