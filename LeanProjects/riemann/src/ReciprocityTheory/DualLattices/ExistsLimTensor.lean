import ReciprocityTheory.DualLattices.NsmulKerZero

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma tw_πr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact (Tw.r_π n x).symm

lemma tw_qr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact Tw.r_q n x

lemma lift_down (Tw : ATowerL R₀ p) (n : ℕ) (τ1 : B.G Tw.O) (th1 : B.G (Tw.R' (n + 1)))
    (w1 : B.gg ⊗[R₀] (Tw.R' (n + 1) : Type u)) (h1 : B.map (Tw.π (n + 1)) th1 = B.map (Tw.q (n + 1)) τ1)
    (h2 : (p ^ (n + 1 + 1)) • th1 = B.tg (Tw.π (n + 1)) (Tw.sqZero (n + 1))
      (TensorProduct.map LinearMap.id (ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1))) w1)) :
    B.map (Tw.π n) (p • B.map (Tw.r' n) th1) = B.map (Tw.q n) (p • τ1) ∧
    (p ^ (n + 1)) • (p • B.map (Tw.r' n) th1) = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n))
        (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1)) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1) =
      LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
        (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap w1) := by
  have e1 : B.map (Tw.π n) (B.map (Tw.r' n) th1) = B.map (Tw.q n) τ1 := by
    rw [← B.map_comp, tw_πr Tw n, B.map_comp, h1, ← B.map_comp, tw_qr Tw n]
  have hf : ∀ a ∈ (Tw.π (n + 1)).ker, (Tw.r' n).1.toLinearMap a ∈ (Tw.π n).ker := by
    intro a ha
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
    rw [AlgHom.toLinearMap_apply, ← Tw.r_π n a, ha, map_zero]
  have hcomm : ((Tw.r' n).1.toLinearMap.restrict hf) ∘ₗ
      ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1)) =
      ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) ∘ₗ (Tw.r' n).1.toLinearMap := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    show (Tw.r' n).1 (Tw.ξ (n + 1) * a) = Tw.ξ n * (Tw.r' n).1 a
    rw [map_mul, Tw.r'_ξ n]
  have h3 : (Tw.π n).1.toLinearMap ∘ₗ (Tw.r' n).1.toLinearMap =
      (Tw.r n).1.toLinearMap ∘ₗ (Tw.π (n + 1)).1.toLinearMap :=
    LinearMap.ext fun a => (Tw.r_π n a).symm
  refine ⟨by rw [map_nsmul, map_nsmul, e1], ?_, ?_⟩
  · rw [smul_smul, ← pow_succ, ← map_nsmul, h2,
      ← B.tg_nat (Tw.π (n + 1)) (Tw.π n) (Tw.sqZero (n + 1)) (Tw.sqZero n) (Tw.r' n) hf]
    have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) hcomm
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply] at h
    exact congrArg (B.tg (Tw.π n) (Tw.sqZero n)) h
  · have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) h3
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using h

def coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (k : Module.Free.ChooseBasisIndex R₀ B.gg) :
    B.gg ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M ((Module.Free.chooseBasis R₀ B.gg).coord k)

lemma coordK_lTensor {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m => simp [coordK]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma sum_coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m =>
    simp only [coordK, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

lemma exists_lim_tensor (Tw : ATowerL R₀ p) (wb : ∀ n, B.gg ⊗[R₀] (Tw.R n : Type u))
    (hwb : ∀ n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap (wb (n + 1)) = wb n) :
    ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n, LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt = wb n := by
  choose a ha using fun k => Tw.complete (fun n => B.coordK (Tw.R n) k (wb n)) (fun n => by
    rw [← hwb n, B.coordK_lTensor]
    rfl)
  refine ⟨∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] a k, fun n => ?_⟩
  rw [map_sum]
  simp only [LinearMap.lTensor_tmul]
  conv_rhs => rw [← B.sum_coordK _ (wb n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ha k n]
  rfl

end BX

end ReciprocityTheory.PGsh
