import Mathlib
open TensorProduct

namespace GlobalTheory

theorem isSMulRegular_of_smul_eq_zero_imp {A X : Type} [CommRing A] [AddCommGroup X] [Module A X]
    (f : A) (h : ∀ x : X, f • x = 0 → x = 0) : IsSMulRegular X f := by
  intro a b hab
  have : f • (a - b) = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (h _ this)

theorem rTensor_lsmul_apply_eq_smul {A X Y : Type} [CommRing A] [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : A) (t : X ⊗[A] Y) :
    (LinearMap.lsmul A X f).rTensor Y t = f • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb, smul_add]

theorem isSMulRegular_tensor_of_flat_quot (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M]
    [Module A M] (hM : IsSMulRegular M f)
    (hfl : Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M))
    (N : Type) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f) :
    IsSMulRegular (TensorProduct A N M) f := by
  classical
  set I : Ideal A := Ideal.span {f} with hI
  haveI := hfl
  let B := A ⧸ I
  let F := M →₀ A
  let π : F →ₗ[A] M := Finsupp.linearCombination A id
  have hπ : Function.Surjective π := Finsupp.linearCombination_id_surjective A M
  let K := LinearMap.ker π
  let ι : K →ₗ[A] F := K.subtype
  have hex : Function.Exact ι π := LinearMap.exact_subtype_ker_map π
  have kerq : ∀ {X : Type} [AddCommGroup X] [Module A X] (x : X),
      ((1 : B) ⊗ₜ[A] x = 0) ↔ ∃ y, f • y = x := by
    intro X _ _ x
    rw [← (quotTensorEquivQuotSMul X I).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
      Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb : Function.Injective (ι.lTensor B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨k, rfl⟩ : ∃ k : K, (1 : B) ⊗ₜ[A] k = x := by
      obtain ⟨k, hk⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul K I x)
      refine ⟨k, (quotTensorEquivQuotSMul K I).injective ?_⟩
      rw [quotTensorEquivQuotSMul_mk_one_tmul, hk]
    rw [LinearMap.lTensor_tmul] at hx
    obtain ⟨y, hy⟩ := (kerq (ι k)).1 hx
    have hy0 : π y = 0 := by
      apply hM
      show f • π y = f • 0
      rw [smul_zero, ← map_smul, hy]
      simpa [ι] using k.2
    rw [kerq]
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let P := B ⊗[A] N
  have hc : Function.Injective (ι.lTensor P) := by
    have hsurjB : Function.Surjective (π.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective _ hπ
    have hinjB : Function.Injective (ι.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]; exact hb
    have hexB : Function.Exact (ι.baseChange B) (π.baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact B hex hπ
    have h := LinearMap.lTensor_injective_of_exact_of_flat (π.baseChange B) hsurjB (ι.baseChange B)
      hinjB hexB P
    let cK := AlgebraTensorModule.cancelBaseChange A B B P K
    let cF := AlgebraTensorModule.cancelBaseChange A B B P F
    have nat : ∀ v, ι.lTensor P (cK v) = cF ((ι.baseChange B).lTensor P v) := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul p y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b k => simp [cK, cF]
        | add a c ha hc => simp_all [tmul_add]
      | add a c ha hc => simp_all
    intro u v huv
    obtain ⟨u, rfl⟩ := cK.surjective u
    obtain ⟨v, rfl⟩ := cK.surjective v
    rw [nat, nat] at huv
    rw [h (cF.injective huv)]
  have hfB : algebraMap A B f = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self f
  have killP : ∀ t : P ⊗[A] F, f • t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p x => rw [smul_tmul', ← algebraMap_smul B f p, hfB, zero_smul, zero_tmul]
    | add a c ha hc => rw [smul_add, ha, hc, add_zero]
  let q : N →ₗ[A] P := TensorProduct.mk A B N 1
  have hqs : Function.Surjective q := by
    intro t
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul N I t)
    refine ⟨n, ?_⟩
    apply (quotTensorEquivQuotSMul N I).injective
    rw [← hn]
    show quotTensorEquivQuotSMul N I ((1 : B) ⊗ₜ[A] n) = _
    rw [quotTensorEquivQuotSMul_mk_one_tmul]
  have hqex : Function.Exact (LinearMap.lsmul A N f) q := by
    intro n
    simp only [q, TensorProduct.mk_apply, Set.mem_range, LinearMap.lsmul_apply]
    exact kerq n
  have ha : IsSMulRegular (N ⊗[A] F) f := by
    have hinj : Function.Injective ((LinearMap.lsmul A N f).rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => hN (by simpa using h))
    intro a b hab
    apply hinj
    rw [rTensor_lsmul_apply_eq_smul, rTensor_lsmul_apply_eq_smul]
    exact hab
  apply isSMulRegular_of_smul_eq_zero_imp
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective N hπ y
  have h1 : π.lTensor N (f • z) = 0 := by rw [map_smul, hy]
  obtain ⟨w, hw⟩ := (lTensor_exact N hex hπ (f • z)).1 h1
  have h2 : ι.lTensor P (q.rTensor K w) = 0 := by
    have : ι.lTensor P (q.rTensor K w) = q.rTensor F (ι.lTensor N w) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    rw [this, hw, map_smul, killP]
  have h3 : q.rTensor K w = 0 := by
    apply hc
    rw [h2, map_zero]
  obtain ⟨w', hw'⟩ := (rTensor_exact K hqex hqs w).1 h3
  rw [rTensor_lsmul_apply_eq_smul] at hw'
  have h4 : z = ι.lTensor N w' := by
    apply ha
    show f • z = f • ι.lTensor N w'
    rw [← map_smul, hw', hw]
  rw [h4]
  exact (lTensor_exact N hex hπ).apply_apply_eq_zero w'

end GlobalTheory
