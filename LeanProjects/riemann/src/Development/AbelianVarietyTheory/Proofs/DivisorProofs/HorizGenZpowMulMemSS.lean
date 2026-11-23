import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecMulAndConstTermMul

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.HorizMul

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_zpow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℤ) (x : Frame X.Ψ r) :
    X.pnorm (m • la) (fun y => P y ^ m) x = X.pnorm la P x ^ m := by
  unfold Data.pnorm
  rw [mul_zpow, norm_zpow, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem differentiable_matDet {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem horizGen_rmul' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (x b : Frame Ψ r) :
    horizGen τ (rmul x b) = horizGen τ x * horizGen τ b := by
  show (mat x τ * mat b τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv]
  rfl

theorem horizGen_lact' {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (γ : GL (Fin r) E) (x : Frame Ψ r) :
    horizGen τ (lact γ x) = (τ.1 γ.1.det)⁻¹ * horizGen τ x := by
  show (γ.1.map τ.1 * mat x τ).det⁻¹ = _
  rw [Matrix.det_mul, mul_inv, RingHom.map_det]
  rfl

theorem bchar_zsmul_modelFlat {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (m : ℤ) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    bchar (m • modelFlat r τ) b = horizGen τ b ^ m := by
  classical
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    Matrix.det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  unfold bchar
  rw [Finset.prod_eq_single τ (fun τ' _ h => by simp [modelFlat, h]) (by simp)]
  simp only [Pi.smul_apply, modelFlat, if_true, smul_eq_mul, mul_neg, mul_one]
  rw [Finset.prod_zpow, horizGen, hd, inv_zpow', zpow_neg]

theorem isBddSec_horizGen_zpow (X : Data E r) (τ : X.Ψ) (m : ℤ)
    (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) (hχ : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1) :
    X.IsBddSec (m • modelFlat r τ) fun y => horizGen τ y ^ m := by
  refine ⟨⟨fun y hy => ?_, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, Real.sqrt ‖τ.1 X.Gm.det‖ ^ m, fun y hy => ?_⟩
  · have hne : (mat y τ).det ≠ 0 := (hy τ).1
    exact (((differentiable_matDet τ y).inv hne).zpow (Or.inl (inv_ne_zero hne))).differentiableWithinAt
  · beta_reduce
    rw [horizGen_rmul', mul_zpow, bchar_zsmul_modelFlat τ m hb, mul_comm]
  · beta_reduce
    rw [horizGen_lact', hdet γ hγ, map_one, inv_one, one_mul, hχ γ hγ, one_mul]
  · rw [pnorm_zpow, pnorm_horizGen X τ hy]

theorem chi_zsmul_modelFlat (X : Data E r) (τ : X.Ψ) (la : Wt X.Ψ r) (m : ℤ)
    (hχ : ∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) : ∀ γ ∈ X.Γ, X.χ (m • modelFlat r τ) γ = 1 := by
  intro γ hγ
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h0 : X.χ la γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := (X.χ_add la (m • modelFlat r τ) γ hγ).symm.trans (hχ γ hγ)
  exact mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)

theorem horizGen_zpow_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (τ : X.Ψ)
    (la : Wt X.Ψ r) (m : ℤ), (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) →
    (∀ γ ∈ X.Γ, X.χ (la + m • modelFlat r τ) γ = X.χ la γ) →
    ∀ P ∈ X.SS la, (fun y => horizGen τ y ^ m * P y) ∈ X.SS (la + m • modelFlat r τ) := by
  intro E _ _ _ r X τ la m hdet hχ P hP
  have hQ := isBddSec_horizGen_zpow X τ m hdet (chi_zsmul_modelFlat X τ la m hχ)
  obtain ⟨hb, hfj⟩ := GlobalTheory.bddSec_mul_and_constTerm_mul E r X la _ P _ hP.1 hQ
  have e : (fun y => horizGen τ y ^ m * P y) = P * fun y => horizGen τ y ^ m := funext fun y => mul_comm _ _
  rw [e]
  refine ⟨hb, fun ξ hξ x hx => ?_⟩
  rw [hfj ξ hξ x hx, hP.2 ξ hξ x hx, zero_mul]

end GlobalTheory.FlatCore.HorizMul
