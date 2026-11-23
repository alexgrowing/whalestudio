import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.Places

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Module Set PiTensorProduct

open scoped TensorProduct RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem contract_tensorRep_single [DecidableEq ι] (π : ∀ v, Representation ℂ (G v) (V v))
    {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)} (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι)
    (g : G v) (t : ⨂[ℂ] w, V w) :
    contract ξ l hl v (tensorRep K π (singleHom K v g) t) = π v g (contract ξ l hl v t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    have h1 : tensorRep K π (singleHom K v g) (tprod ℂ x) =
        tprod ℂ (Function.update x v (π v g (x v))) := tensorRep_mulSingle_tprod v g x
    rw [h1]
    by_cases hx : IsRestricted ξ x
    · rw [contract_tprod v (hx.update v _), contract_tprod v hx, map_smul,
        weight_update_of_mem l x (Finset.mem_singleton_self v), Function.update_self]
    · have hx' : ¬ IsRestricted ξ (Function.update x v (π v g (x v))) :=
        fun h => hx (isRestricted_update_iff.1 h)
      rw [contract, lift.tprod, lift.tprod]
      show restrictedIndicator ξ _ • _ = π v g (restrictedIndicator ξ x • _)
      rw [restrictedIndicator_of_not hx, restrictedIndicator_of_not hx', zero_smul, zero_smul,
        map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {V' : ι → Type*} [∀ v, AddCommGroup (V' v)] [∀ v, Module ℂ (V' v)]

theorem nonempty_equiv_of_restrictedTensorRep_equiv {π : ∀ v, Representation ℂ (G v) (V v)}
    {π' : ∀ v, Representation ℂ (G v) (V' v)} {ξ : ∀ v, V v} {ξ' : ∀ v, V' v}
    (hirr : ∀ v, (π v).IsIrreducible) (hirr' : ∀ v, (π' v).IsIrreducible)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ' : ∀ᶠ v in cofinite, ξ' v ∈ fixedVectors (π' v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0) (hξ'0 : ∀ᶠ v in cofinite, ξ' v ≠ 0)
    (Φ : (restrictedTensorRep π ξ hξ).Equiv (restrictedTensorRep π' ξ' hξ')) (v : ι) :
    Nonempty ((π v).Equiv (π' v)) := by
  classical
  haveI := hirr v
  haveI := hirr' v
  have hnt : ∀ w, ∃ u : V w, u ≠ 0 := fun w =>
    have := nontrivial_of_isIrreducible (hirr w)
    exists_ne 0
  choose e he using hnt
  set ξ₀ : ∀ w, V w := fun w => if ξ w = 0 then e w else ξ w
  have hξ₀ : IsRestricted ξ ξ₀ := hξ0.mono fun w h => by simp [ξ₀, h]
  have hξ₀0 : ∀ w, ξ₀ w ≠ 0 := fun w => by
    by_cases h : ξ w = 0 <;> simp [ξ₀, h, he w]

  let ins : V v →ₗ[ℂ] restrictedTensor ξ :=
    LinearMap.codRestrict (restrictedTensor ξ) ((PiTensorProduct.tprod ℂ).toLinearMap ξ₀ v)
      fun u => tprod_mem_restrictedTensor (hξ₀.update v u)
  have hins : ∀ u, (ins u : ⨂[ℂ] w, V w) = tprod ℂ (Function.update ξ₀ v u) := fun u => rfl
  have hinsg : ∀ (g : G v) u, ins (π v g u) = restrictedTensorRep π ξ hξ (singleHom K v g) (ins u) :=
    fun g u => Subtype.ext (by
      rw [coe_restrictedTensorRep_apply, hins, hins]
      exact (tensorRep_mulSingle_tprod (K := K) (π := π) v g _).trans (by
        rw [Function.update_idem, Function.update_self]) |>.symm)
  have hy0 : ins (e v) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    rw [hins] at this
    refine tprod_ne_zero (ξ := ξ) (hξ₀.update v (e v)) (fun w => ?_) this
    by_cases hw : w = v
    · subst hw; simp [he]
    · simp [Function.update_of_ne hw, hξ₀0 w]
  have hΦy : ((Φ (ins (e v)) : restrictedTensor ξ') : ⨂[ℂ] w, V' w) ≠ 0 := by
    intro h
    apply hy0
    have : Φ (ins (e v)) = 0 := Subtype.ext h
    exact Φ.toLinearEquiv.injective (this.trans (map_zero _).symm)
  obtain ⟨l', hl', hne⟩ := exists_evalForm_ne_zero hξ'0 (Φ (ins (e v))).2 hΦy

  let μ : Dual ℂ (V v) := evalForm ξ' l' hl' ∘ₗ (restrictedTensor ξ').subtype ∘ₗ
    Φ.toLinearEquiv.toLinearMap ∘ₗ ins
  refine nonempty_equiv_of_matrixCoeff_eq (v := e v) (l := μ)
    (w := contract ξ' l' hl' v (Φ (ins (e v)))) (m := l' v) (fun g => ?_) ⟨1, ?_⟩
  · have hΦ : ∀ (h : Πʳ w, [G w, K w]) (x : restrictedTensor ξ),
        Φ (restrictedTensorRep π ξ hξ h x) = restrictedTensorRep π' ξ' hξ' h (Φ x) :=
      fun h x => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap h x
    show evalForm ξ' l' hl' (Φ (ins (π v g (e v))) : ⨂[ℂ] w, V' w) = _
    rw [hinsg, hΦ, coe_restrictedTensorRep_apply, ← apply_contract v, contract_tensorRep_single]
  · show evalForm ξ' l' hl' (Φ (ins (π v 1 (e v))) : ⨂[ℂ] w, V' w) ≠ 0
    rw [map_one, Module.End.one_apply]
    exact hne

end RestrictedTensor

end GroundTheory.Automorphic
