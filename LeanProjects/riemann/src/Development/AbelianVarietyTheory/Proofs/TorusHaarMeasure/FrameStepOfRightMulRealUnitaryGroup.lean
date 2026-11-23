import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.UnitaryLift

open GlobalTheory.UnitaryFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma conj_unitary {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) :
    X.IsUnitaryC fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) := by
    congr 1
    funext k
    unfold sgn
    split_ifs <;> simp
  have hy : IsOrth X
      (fun τ => (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    intro τ
    have h0 := hx0 τ
    rw [gram_eq_mul, hJ] at h0
    change gram τ.1 X.Gm (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [gram_eq_mul, hJ, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
          ((mat x0 τ)ᵀ * (X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ))) *
          (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h0, hc τ]
  have he : toGL X hy = toGL X hx0 * c := by
    funext τ
    exact Units.ext rfl
  rw [← he]
  exact quotient_unitary X hy hx0

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag {r p : ℕ} {a : Matrix (Fin r) (Fin r) ℂ}
    (ha : aᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) *
      a.map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1)) : a.det ≠ 0 := by
  have hD : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    split_ifs <;> norm_num
  intro h0
  have h := congrArg Matrix.det ha
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at h
  exact hD h.symm

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma conj_mul_inv_preserves_gram {r : ℕ} (G D M b : Matrix (Fin r) (Fin r) ℂ)
    (hM : IsUnit M.det) (hG : Mᵀ * (G * M.map (starRingEnd ℂ)) = D)
    (hb : bᵀ * D * b.map (starRingEnd ℂ) = D) :
    (M * b * M⁻¹)ᵀ * (G * (M * b * M⁻¹).map (starRingEnd ℂ)) = G := by
  obtain ⟨P, hP⟩ : ∃ P, P = M * b * M⁻¹ := ⟨_, rfl⟩
  rw [← hP]
  have hPM : P * M = M * b := by
    rw [hP, mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hM, mul_one]
  have hT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  have hC : IsUnit (M.map (starRingEnd ℂ)).det := by
    have := (RingHom.map_det (starRingEnd ℂ) M).symm
    rw [show (starRingEnd ℂ).mapMatrix M = M.map (starRingEnd ℂ) from rfl] at this
    rw [this]
    exact hM.map _
  have key : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
      Mᵀ * G * M.map (starRingEnd ℂ) := by
    have e1 : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
        (P * M)ᵀ * G * (P * M).map (starRingEnd ℂ) := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [e1, hPM, Matrix.transpose_mul, Matrix.map_mul]
    calc bᵀ * Mᵀ * G * (M.map (starRingEnd ℂ) * b.map (starRingEnd ℂ))
        = bᵀ * (Mᵀ * (G * M.map (starRingEnd ℂ))) * b.map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = Mᵀ * G * M.map (starRingEnd ℂ) := by
          rw [hG, hb, ← hG, Matrix.mul_assoc]
  calc Pᵀ * (G * P.map (starRingEnd ℂ))
      = (Mᵀ)⁻¹ * (Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ))⁻¹ := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]
    _ = (Mᵀ)⁻¹ * (Mᵀ * G * M.map (starRingEnd ℂ)) * (M.map (starRingEnd ℂ))⁻¹ := by rw [key]
    _ = G := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UnitaryLift.step_of_right_mul :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  classical
  intro r X H hH x0 hx0 τ0 a s ha hs hsa
  have hM : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).det :=
    isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx0 τ0)
  have ha' : IsUnit a.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag ha)
  have hs' : IsUnit s.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag hs)
  have horth : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)ᵀ * (X.Gm.map (τ0 : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).map (starRingEnd ℂ)) =
      Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1 := by
    have h := hx0
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at h
    have h := h τ0
    rw [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul] at h
    rw [h]
    congr 1
    funext k
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  let ν : GL (Fin r) ℂ := Matrix.nonsingInvUnit _ hM
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) →
      (Pi.mulSingle τ0 (ν * b * ν⁻¹) : X.Ψ → GL (Fin r) ℂ) ∈ H := by
    intro b hb
    rw [hH]
    intro τ u w
    by_cases hτ : τ = τ0
    · beta_reduce
      rw [hτ, Pi.mulSingle_eq_same]
      have hcoe : ((ν * b * ν⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * b * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := rfl
      rw [hcoe, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, _root_.GlobalTheory.UnitaryFrames.gram_eq_mul,
        conj_mul_inv_preserves_gram _ _ _ _ hM horth hb, _root_.GlobalTheory.UnitaryFrames.hermC_eq_dot]
    · beta_reduce
      rw [Pi.mulSingle_eq_of_ne hτ, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]
  let αa : GL (Fin r) ℂ := Matrix.nonsingInvUnit a ha'
  let σ : GL (Fin r) ℂ := Matrix.nonsingInvUnit s hs'
  have hσ : σ * αa = αa⁻¹ * σ := Units.ext hsa
  have hσ' : σ * αa⁻¹ = αa * σ := by
    calc σ * αa⁻¹ = αa * (αa⁻¹ * σ) * αa⁻¹ := by group
      _ = αa * (σ * αa) * αa⁻¹ := by rw [hσ]
      _ = αa * σ := by group
  let hh : H := (⟨_, hmem αa ha⟩ : H)⁻¹
  have hh0 : ((hh : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := by
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_same]
    rw [show (ν * αa * ν⁻¹)⁻¹ = ν * αa⁻¹ * ν⁻¹ by group]
    rfl
  have hhne : ∀ τ, τ ≠ τ0 → ((hh : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    intro τ hτ
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_of_ne hτ, inv_one, Units.val_one]
  refine ⟨hh, ⟨_, hmem σ hs⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul]
    congr 1
    calc ν * σ * ν⁻¹ * (ν * αa * ν⁻¹)⁻¹ = ν * (σ * αa⁻¹) * ν⁻¹ := by group
      _ = ν * (αa * σ) * ν⁻¹ := by rw [hσ']
      _ = ν * αa * ν⁻¹ * (ν * σ * ν⁻¹) := by group
  · intro g
    refine funext fun τ => ?_
    by_cases hτ : τ = τ0
    · rw [hτ]
      refine Eq.trans ?_ (@Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) τ0 _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 =
        ((g : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hh0, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_right _ _ hM, Matrix.mul_assoc]
    · refine Eq.trans ?_ (@Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ hτ _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ =
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hhne τ hτ, Matrix.mul_one]

end GlobalTheory.UnitaryLift
