import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousPair

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

theorem mq_add' (S T : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (S + T) g = mq S g + mq T g := by
  ext x
  simp only [mq_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, inner_add_right]
  push_cast
  ring

theorem mq_smul' (c : ℝ) (S : Eu l →L[ℝ] Eu l) (g : Sch l) : mq (c • S) g = c • mq S g := by
  ext x
  simp only [mq_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.real_smul]
  push_cast
  ring

theorem vf_add' (H K : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (H + K) g = vf H g + vf K g := by
  ext x
  simp only [vf_apply, SchwartzMap.add_apply, ContinuousLinearMap.add_apply, map_add]

theorem vf_smul' (c : ℝ) (H : Eu l →L[ℝ] Eu l) (g : Sch l) : vf (c • H) g = c • vf H g := by
  ext x
  simp only [vf_apply, SchwartzMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]

def qdLin (f : Sch l) : Mat l →ₗ[ℝ] Sch l where
  toFun X := Qd X f
  map_add' X Y := by
    have ht : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    simp only [Qd, map_add, neg_add, mq_add', vf_add', ht, trace_add, add_div, ofReal_add, add_smul]
    abel
  map_smul' c X := by
    have ht : (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    have hc : ((c • X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f = c • (((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f) := by
      rw [smul_eq_mul, mul_div_assoc, ofReal_mul, mul_smul, Complex.coe_smul]
    simp only [Qd, map_smul, ← smul_neg, mq_smul', vf_smul', ht, trace_smul, RingHom.id_apply]
    rw [hc, (fou l).map_smul_of_tower, smul_sub, smul_add, smul_add]

theorem qd_sum (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by
  show _ = qdLin f X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  rfl

theorem exp_mem_sp {X : Mat l} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    NormedSpace.exp X ∈ Matrix.symplecticGroup l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [SymplecticGroup.mem_iff', Matrix.mul_assoc]
  exact h2

theorem onePar_of (h1 : TopG l) (h2 : Cover l) (h3 : NearOne l) (h4 : SecDer l) : OnePar l := by
  have : IsTopologicalGroup (G l) := h1
  intro X hX
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ := fun t =>
    exp_mem_sp (SMulMemClass.smul_mem t hX)
  have hcont : Continuous fun t : ℝ => (NormedSpace.exp (t • X) : Mat l) :=
    continuous_pi fun a => continuous_pi fun b => continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X t).continuousAt
  let p : C(ℝ, Sp l) := ⟨fun t => ⟨NormedSpace.exp (t • X), hmem t⟩, hcont.subtype_mk _⟩
  have hp : ∀ t, (p t).1 = NormedSpace.exp (t • X) := fun t => rfl
  have hpadd : ∀ s t, p (s + t) = p s * p t := fun s t => Subtype.ext (by
    show NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have he : pr (1 : G l) = p 0 := by
    rw [map_one]
    exact Subtype.ext (by simp [hp])
  obtain ⟨Γ, ⟨hΓ0, hΓp⟩, -⟩ := h2.existsUnique_continuousMap_lifts p 0 1 he
  have hpr : ∀ t, pr (Γ t) = p t := fun t => congrFun hΓp t
  refine ⟨Γ, Γ.continuous, hΓ0, fun s t => ?_, fun t => by rw [hpr]; rfl, fun f => ?_⟩
  · have := h2.eq_of_comp_eq (g₁ := fun t => Γ (s + t)) (g₂ := fun t => Γ s * Γ t)
      (Γ.continuous.comp (continuous_const.add continuous_id)) (continuous_const.mul Γ.continuous)
      (funext fun t => by simp only [Function.comp, map_mul, hpr, hpadd]) 0 (by simp [hΓ0])
    exact congrFun this t
  · have h3' : ∀ᶠ g in 𝓝 (Γ 0), omS g = sec (pr g).1 := by rw [hΓ0]; exact h3
    have hev := (Γ.continuous.tendsto 0).eventually h3'
    have hd : ∀ a b, HasFDerivAt (fun x : ℝ => NormedSpace.exp (x • X) a b)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0 := fun a b => by
      have := hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X 0
      simp only [zero_smul, NormedSpace.exp_zero, one_mul, Matrix.entryLinearMap_apply] at this
      exact this.hasFDerivAt
    have hS := (h4 ℝ (fun x => NormedSpace.exp (x • X)) (fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (X a b)) 0
      (by simp) hd f).hasDerivAt
    have hval : (∑ a, ∑ b, ((1 : ℝ →L[ℝ] ℝ).smulRight (X a b)).smulRight
        (schwartzToL2 l (Qd (Matrix.single a b 1) f))) 1 = (quad X f).toLp 2 := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, one_smul]
      rw [show quad X f = Qd X f from quad_eq hX f, ← qd_sum X f]
      show _ = schwartzToL2 l _
      simp only [map_sum, ContinuousLinearMap.map_smul_of_tower]
    rw [hval] at hS
    refine hS.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    show om (Γ t) (schwartzToL2 l f) = _
    rw [om_sch, ht, hpr t]
    rfl

end PositivityTheory.ThKR.Mp
