import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.RegEmbed

variable {K Γ R : Type} [Field K] [Group Γ] [CommRing R] [Algebra K R]
  (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H]

theorem act_mul_apply (a b : Γ) (x : R) : act (a * b) x = act a (act b x) := by
  rw [map_mul]; rfl

theorem act_one_apply (x : R) : act 1 x = x := by
  rw [map_one]; rfl

theorem sum_act_act (x : R) (g : H) : ∑ k : H, act k (act g x) = ∑ k : H, act k x := by
  rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [← act_mul_apply]

theorem act_sum_act (x : R) (g : H) : act g (∑ k : H, act k x) = ∑ k : H, act k x := by
  rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.coe_mulLeft, ← act_mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

def invIn (V₁ : Submodule K R) : Submodule K R where
  carrier := {x | x ∈ V₁ ∧ ∀ h : H, act h x = x}
  add_mem' := fun ha hb => ⟨V₁.add_mem ha.1 hb.1, fun h => by rw [map_add, ha.2, hb.2]⟩
  zero_mem' := ⟨V₁.zero_mem, fun h => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V₁.smul_mem c hx.1, fun h => by rw [map_smul, hx.2]⟩

def trL : R →ₗ[K] R := ∑ g : H, (act g).toLinearMap

theorem trL_apply (x : R) : trL act H x = ∑ g : H, act g x := by
  simp [trL]

theorem trL_mem (V₁ : Submodule K R) (hV₁ : ∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) (x : R) (hx : x ∈ V₁) :
    trL act H x ∈ invIn act H V₁ := by
  rw [trL_apply]
  exact ⟨V₁.sum_mem fun g _ => hV₁ g x hx, fun g => act_sum_act act H x g⟩

theorem eq_zero_of_traces [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (v : R)
    (hv : ∀ h : H, ∑ g : H, act g (v * act h u) = 0) : v = 0 := by
  have h0 := GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u))
    (by rwa [Matrix.det_transpose]) (fun g : H => act g v) (by
      funext h
      rw [Pi.zero_apply, ← hv h]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul (act (g : Γ)), act_mul_apply, mul_comm])
  simpa [act_one_apply] using congrFun h0 1

theorem eq_zero_of_sum [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (F : H → R)
    (hF : ∀ g h : H, act g (F h) = F h) (h0 : ∑ h : H, F h * act h u = 0) : F = 0 := by
  refine GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor _ hdet F ?_
  funext g
  have h2 := congrArg (fun x => act (g : Γ) x) h0
  simp only [map_sum, map_zero] at h2
  rw [Pi.zero_apply, ← h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (act (g : Γ)), hF, act_mul_apply, mul_comm]

end GlobalTheory.RegEmbed

namespace GlobalTheory.BadCount

open GlobalTheory.RegEmbed in

theorem embReg_of_groupDet : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V₁ V₂ : Submodule K R) [FiniteDimensional K V₂] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, x * act h u ∈ V₂) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V₂ := by
  intro K Γ R _ _ _ _ _ act H _ _ u hdet V V₁ V₂ _ ρ hρ hV hV₁ hV₁₂
  let I := invIn act H V₁
  let T : H → (V →ₗ[K] I) := fun h =>
    ((trL act H).comp ((LinearMap.mulRight K (act h u)).comp V.subtype)).codRestrict I
      (fun v => trL_mem act H V₁ hV₁ _ (hV h v v.2))
  have hT : ∀ h v, ((T h v : I) : R) = ∑ g : H, act g (v * act h u) := fun h v => by
    simp [T, trL_apply]
  let Ψ : (H → I) →ₗ[K] V₂ :=
    (∑ h : H, (LinearMap.mulRight K (act h u)).comp (I.subtype.comp (LinearMap.proj h))).codRestrict V₂
      (fun F => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        exact V₂.sum_mem fun h _ => hV₁₂ h _ (F h).2.1)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_sum act H u hdet (fun h => (F h : R)) (fun g h => (F h).2.2 g) (by
      have := congrArg Subtype.val hF
      simpa [Ψ] using this)
    funext h
    exact Subtype.ext (congrFun h0 h)
  haveI : Module.Finite K (H → I) := Module.Finite.of_injective Ψ hΨ
  haveI : Module.Finite K I :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : H => I) 1) (fun x => ⟨fun _ => x, rfl⟩)
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  let b := Module.finBasis K I
  let j : V →ₗ[K] (Fin (finrank K I) → MonoidAlgebra K H) := LinearMap.pi fun i =>
    (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite K K H).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun h => (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap) ∘ₗ T h)
  have hj : ∀ v i h, (j v i).coeff h = b.equivFun (T h v) i := fun v i h => by
    simp [j]
  refine ⟨finrank K I, ⟨j, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hTv : ∀ h, T h v = 0 := fun h => by
      apply b.equivFun.injective
      funext i
      rw [← hj, hv]
      simp
    apply Subtype.ext
    refine eq_zero_of_traces act H u hdet (v : R) fun h => ?_
    rw [← hT, hTv]
    rfl
  · intro h v i
    apply MonoidAlgebra.ext
    ext k
    rw [MonoidAlgebra.single_mul_apply, one_mul, hj, hj]
    have : T k (ρ h v) = T (h⁻¹ * k) v := by
      apply Subtype.ext
      rw [hT, hT, hρ]
      conv_rhs => rw [← sum_act_act act H _ h]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      rw [map_mul (act (h : Γ)), Subgroup.coe_mul, Subgroup.coe_inv, ← act_mul_apply act (h : Γ) ((h : Γ)⁻¹ * k),
        mul_inv_cancel_left]
    rw [this]
  · rw [Nat.card_eq_fintype_card, mul_comm]
    exact hle

end GlobalTheory.BadCount
