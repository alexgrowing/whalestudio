import Formalism.RealPlaceAnalysis.StatementU

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section U3Basic
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem indexArray_ext {F G : Arr V n j} (h : ∀ α, F α = G α) : F = G := by
  exact PiLp.ext h

theorem factorAction_apply (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  unfold factorAction
  by_cases h1 : (α i).1 = c <;> by_cases h2 : (α i).2 = d <;> simp [h1, h2, arrTo, arrOf]

theorem pointwiseAction_apply (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : ptE E c d F α = E c d (F α) := by
  rfl

theorem permutePositions_apply (σ : Equiv.Perm (Fin j)) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    permArr V n σ F α = F (fun i => α (σ i)) := by
  rfl

theorem firstPositionSlice_apply (α' : Fin j → Fin n × Fin n) (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' F β = F (Fin.cons (β 0) α') := by
  rfl

theorem indexArray_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Arr V n j) (α : Fin j → Fin n × Fin n) :
    (∑ i ∈ s, f i) α = ∑ i ∈ s, f i α := by
  exact map_sum (LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) f s

theorem mem_admissibleArrays (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (u : V) (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by
  simp only [arrV0, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem sum_update_involution {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] (i : Fin j)
    (σ : X → X) (hσ : ∀ x, σ (σ x) = x) (P : X → Prop) [DecidablePred P]
    (f : (Fin j → X) → (Fin j → X) → M) :
    ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (σ (α i))) α else 0) =
      ∑ β : Fin j → X, (if P (σ (β i)) then f β (Function.update β i (σ (β i))) else 0) := by
  classical
  have hinv : Function.Involutive (fun α : Fin j → X => Function.update α i (σ (α i))) := by
    intro α
    simp [hσ]
  refine Fintype.sum_bijective _ hinv.bijective _ _ ?_
  intro α
  simp [hσ]

end U3Basic

section U3Inner
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}

theorem indexArray_inner (F G : Arr V n j) : ⟪F, G⟫_ℂ = ∑ α, ⟪F α, G α⟫_ℂ := by
  exact PiLp.inner_apply F G

private theorem sum_update_ite_eq_sum_update_ite_of_involution {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] (i : Fin j)
    (σ τ τ' : X → X) (hσ : ∀ x, σ (σ x) = x) (P Q : X → Prop) [DecidablePred P] [DecidablePred Q]
    (hτ : ∀ x, P x → σ x = τ x) (hτ' : ∀ x, Q x → σ x = τ' x) (hQ : ∀ x, Q x ↔ P (σ x))
    (f : (Fin j → X) → (Fin j → X) → M) :
    ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (τ (α i))) α else 0) =
      ∑ β : Fin j → X, (if Q (β i) then f β (Function.update β i (τ' (β i))) else 0) := by
  have h1 : (∑ α : Fin j → X, (if P (α i) then f (Function.update α i (τ (α i))) α else 0)) =
      ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (σ (α i))) α else 0) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases h : P (α i)
    · rw [if_pos h, if_pos h, hτ _ h]
    · rw [if_neg h, if_neg h]
  rw [h1, sum_update_involution i σ hσ P f]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases h : Q (β i)
  · rw [if_pos ((hQ _).1 h), if_pos h, hτ' _ h]
  · rw [if_neg (fun h' => h ((hQ _).2 h')), if_neg h]

theorem inner_positionAction (i : Fin j) (c d : Fin n) (F G : Arr V n j) :
    ⟪factorAction i c d F, G⟫_ℂ = ⟪F, factorAction i d c G⟫_ℂ := by
  rw [indexArray_inner, indexArray_inner]
  have e1 : ∀ α : Fin j → Fin n × Fin n, ⟪factorAction i c d F α, G α⟫_ℂ =
      (if (α i).1 = c then ⟪F (Function.update α i (d, (α i).2)), G α⟫_ℂ else 0) -
      (if (α i).2 = d then ⟪F (Function.update α i ((α i).1, c)), G α⟫_ℂ else 0) := by
    intro α
    rw [factorAction_apply, inner_sub_left]
    split_ifs <;> simp
  have e2 : ∀ β : Fin j → Fin n × Fin n, ⟪F β, factorAction i d c G β⟫_ℂ =
      (if (β i).1 = d then ⟪F β, G (Function.update β i (c, (β i).2))⟫_ℂ else 0) -
      (if (β i).2 = c then ⟪F β, G (Function.update β i ((β i).1, d))⟫_ℂ else 0) := by
    intro β
    rw [factorAction_apply, inner_sub_right]
    split_ifs <;> simp
  simp only [e1, e2, Finset.sum_sub_distrib]
  congr 1
  · refine sum_update_ite_eq_sum_update_ite_of_involution i (fun p => if p.1 = c then (d, p.2) else if p.1 = d then (c, p.2) else p)
      (fun p => (d, p.2)) (fun p => (c, p.2)) ?_ (fun p => p.1 = c) (fun p => p.1 = d) ?_ ?_ ?_
      (fun x y => ⟪F x, G y⟫_ℂ)
    · rintro ⟨x, y⟩
      by_cases h1 : x = c <;> by_cases h2 : x = d <;> by_cases h3 : d = c <;> simp_all
    · rintro ⟨x, y⟩ h
      simp_all
    · rintro ⟨x, y⟩ h
      by_cases h1 : x = c <;> simp_all
    · rintro ⟨x, y⟩
      by_cases h1 : x = c <;> by_cases h2 : x = d <;> by_cases h3 : d = c <;> simp_all
  · refine sum_update_ite_eq_sum_update_ite_of_involution i (fun p => if p.2 = d then (p.1, c) else if p.2 = c then (p.1, d) else p)
      (fun p => (p.1, c)) (fun p => (p.1, d)) ?_ (fun p => p.2 = d) (fun p => p.2 = c) ?_ ?_ ?_
      (fun x y => ⟪F x, G y⟫_ℂ)
    · rintro ⟨x, y⟩
      by_cases h1 : y = d <;> by_cases h2 : y = c <;> by_cases h3 : c = d <;> simp_all
    · rintro ⟨x, y⟩ h
      simp_all
    · rintro ⟨x, y⟩ h
      by_cases h1 : y = d <;> simp_all
    · rintro ⟨x, y⟩
      by_cases h1 : y = d <;> by_cases h2 : y = c <;> by_cases h3 : c = d <;> simp_all

theorem inner_totalPositionAction (c d : Fin n) (F G : Arr V n j) :
    ⟪positionsE V n j c d F, G⟫_ℂ = ⟪F, positionsE V n j d c G⟫_ℂ := by
  simp only [positionsE, LinearMap.sum_apply, sum_inner, inner_sum, inner_positionAction]

end U3Inner

section U3Cas
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}

theorem compactCasimir_apply (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ W) (x : W) :
    CasK ε T x = ∑ a, ∑ b, if ε a = ε b then T a b (T b a x) else 0 := by
  first
    | simp only [CasK, LinearMap.sum_apply]
    | simp only [CasK, LinearMap.coe_sum, Finset.sum_apply]
    | simp only [CasK, LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> rfl

theorem compactCasimir_add (ε : Fin n → Bool) (S P : Fin n → Fin n → Module.End ℂ W)
    (hc : ∀ a b c d, S a b * P c d = P c d * S a b) :
    CasK ε (fun a b => S a b + P a b) = CasK ε S + CasK ε P +
      2 * ∑ a, ∑ b, (if ε a = ε b then S a b * P b a else 0) := by
  simp only [CasK]
  have hswap : (∑ a, ∑ b, if ε a = ε b then P a b * S b a else 0) =
      ∑ a, ∑ b, if ε a = ε b then S a b * P b a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : ε a = ε b
    · rw [if_pos h.symm, if_pos h, hc]
    · rw [if_neg (Ne.symm h), if_neg h]
  have expand : ∀ a b, (if ε a = ε b then (S a b + P a b) * (S b a + P b a) else 0) =
      (if ε a = ε b then S a b * S b a else 0) + (if ε a = ε b then P a b * P b a else 0) +
      ((if ε a = ε b then S a b * P b a else 0) + (if ε a = ε b then P a b * S b a else 0)) := by
    intro a b
    split_ifs
    · simp only [add_mul, mul_add]
      abel
    · simp
  simp only [expand, Finset.sum_add_distrib, hswap, two_mul]

end U3Cas

section U3CasArr
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem factorAction_mul_pointwiseAction (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) (a b c d : Fin n) :
    factorAction (V := V) i a b * ptE (j := j) E c d = ptE E c d * factorAction i a b := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  change factorAction i a b (ptE E c d F) α = ptE E c d (factorAction i a b F) α
  simp only [factorAction_apply, pointwiseAction_apply]
  split_ifs <;> simp

theorem totalPositionAction_mul_pointwiseAction (E : Fin n → Fin n → Module.End ℂ V) (a b c d : Fin n) :
    positionsE V n j a b * ptE E c d = ptE E c d * positionsE V n j a b := by
  simp only [positionsE, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => factorAction_mul_pointwiseAction E i a b c d

theorem sum_positionMixedCasimir (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    ∑ i : Fin j, OmS ε E i =
      ∑ c, ∑ d, (if ε c = ε d then positionsE V n j c d * ptE E d c else 0) := by
  simp only [OmS, positionsE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : ε c = ε d
  · simp [h, Finset.sum_mul]
  · simp [h]

theorem compactSpan_invariant (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ V) (x : V) :
    KStable ε T (kSpan ε T x) := by
  intro a b hab y hy
  simp only [kSpan, Submodule.mem_sInf, Set.mem_setOf_eq] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem admissibleArrays_apply_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n j}
    (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) : F α ∈ kSpan ε E u := by
  have h := (mem_admissibleArrays ε E u F).1 hF α
  split_ifs at h with hc
  · exact h
  · rw [Submodule.mem_bot] at h
    rw [h]
    exact Submodule.zero_mem _

theorem admissibleArrays_apply_eq_zero {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n j}
    (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) (hα : ¬ ∀ i, ε (α i).1 ≠ ε (α i).2) :
    F α = 0 := by
  have h := (mem_admissibleArrays ε E u F).1 hF α
  rw [if_neg hα, Submodule.mem_bot] at h
  exact h

theorem compactCasimir_pointwiseAction_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : CasK ε (ptE (j := j) E) F α = CasK ε E (F α) := by
  rw [compactCasimir_apply, compactCasimir_apply, indexArray_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [indexArray_sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [pointwiseAction_apply, pointwiseAction_apply]
  · rfl

theorem casArr_of (hk : KCasSpan) : CasArr := by
  intro V _ _ n ε E Λ u j
  refine ⟨fun hgl hkh F hF => ?_, fun F => ?_⟩
  · have hcomm : ∀ a b c d, positionsE V n j a b * ptE E c d = ptE E c d * positionsE V n j a b :=
      fun a b c d => totalPositionAction_mul_pointwiseAction E a b c d
    have hsplit : arrE E j = fun a b => positionsE V n j a b + ptE E a b := rfl
    rw [hsplit, compactCasimir_add ε _ _ hcomm, ← sum_positionMixedCasimir]
    rw [LinearMap.add_apply, LinearMap.add_apply, two_mul, LinearMap.add_apply, LinearMap.sum_apply,
      two_smul]
    congr 1
    congr 1
    refine indexArray_ext fun α => ?_
    rw [compactCasimir_pointwiseAction_apply, PiLp.smul_apply]
    exact hk V n ε E Λ u (fun a b c d _ _ => hgl a b c d) hkh (F α) (admissibleArrays_apply_mem hF α)
  · rw [compactCasimir_apply, inner_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun a _ => ?_
    rw [inner_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    split_ifs
    · rw [← inner_totalPositionAction]
      have hre : (⟪positionsE V n j b a F, positionsE V n j b a F⟫_ℂ).re = ‖positionsE V n j b a F‖ ^ 2 := by
        first
          | exact inner_self_eq_norm_sq _
          | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
          | simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (positionsE V n j b a F)
      rw [hre]
      positivity
    · simp

end U3CasArr

section U3Perm
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem update_comp_perm {X : Type*} (σ : Equiv.Perm (Fin j)) (α : Fin j → X) (i : Fin j) (x : X) :
    (fun k => Function.update α i x (σ k)) = Function.update (fun k => α (σ k)) (σ.symm i) x := by
  funext k
  by_cases hk : k = σ.symm i
  · subst hk
    simp
  · have hk' : σ k ≠ i := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
    simp [Function.update_apply, hk, hk']

theorem factorAction_mul_permuteFactors (σ : Equiv.Perm (Fin j)) (i : Fin j) (c d : Fin n) :
    factorAction (V := V) i c d * permArr V n σ = permArr V n σ * factorAction (σ.symm i) c d := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  change factorAction i c d (permArr V n σ F) α = permArr V n σ (factorAction (σ.symm i) c d F) α
  simp only [factorAction_apply, permutePositions_apply, update_comp_perm, Equiv.apply_symm_apply]

theorem pointwiseAction_mul_permutePositions (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (c d : Fin n) :
    ptE E c d * permArr V n σ = permArr V n σ * ptE E c d := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  rfl

theorem mixedCasimir_mul_permuteFactors (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j))
    (i : Fin j) : OmS ε E i * permArr V n σ = permArr V n σ * OmS ε E (σ.symm i) := by
  simp only [OmS, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · rw [mul_assoc, pointwiseAction_mul_permutePositions, ← mul_assoc, factorAction_mul_permuteFactors, mul_assoc]
  · simp

theorem indexArrayAction_mul_permutePositions (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (a b : Fin n) :
    arrE E j a b * permArr V n σ = permArr V n σ * arrE E j a b := by
  simp only [arrE, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, factorAction_mul_permuteFactors, pointwiseAction_mul_permutePositions]
  congr 1
  exact Equiv.sum_comp σ.symm (fun i => permArr V n σ * factorAction i a b)

theorem mem_symmetricArrays (F : Arr V n j) :
    F ∈ symSub V n j ↔ ∀ σ : Equiv.Perm (Fin j), permArr V n σ F = F := by
  simp [symSub, sub_eq_zero]

theorem sum_fin_cons {X M : Type*} [Fintype X] [AddCommMonoid M] (f : (Fin (j+1) → X) → M) :
    ∑ α, f α = ∑ α' : Fin j → X, ∑ β : Fin 1 → X, f (Fin.cons (β 0) α') := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (j+1) => X)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun α' _ => ?_
  exact ((Equiv.funUnique (Fin 1) X).sum_comp (fun x => f (Fin.cons x α'))).symm

theorem firstPositionSlice_positionAction_zero (α' : Fin j → Fin n × Fin n) (c d : Fin n) (F : Arr V n (j+1)) :
    sliceLin V n α' (factorAction 0 c d F) = factorAction 0 c d (sliceLin V n α' F) := by
  refine indexArray_ext fun β => ?_
  simp [firstPositionSlice_apply, factorAction_apply, Fin.update_cons_zero]

theorem firstPositionSlice_pointwiseAction (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (c d : Fin n)
    (F : Arr V n (j+1)) : sliceLin V n α' (ptE E c d F) = ptE E c d (sliceLin V n α' F) := by
  refine indexArray_ext fun β => ?_
  simp [firstPositionSlice_apply, pointwiseAction_apply]

theorem firstPositionSlice_positionMixedCasimir_zero (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (α' : Fin j → Fin n × Fin n) (F : Arr V n (j+1)) :
    sliceLin V n α' (OmS ε E 0 F) = OmS ε E 0 (sliceLin V n α' F) := by
  first
    | simp only [OmS, LinearMap.sum_apply, map_sum]
    | simp only [OmS, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    | simp only [OmS, LinearMap.coe_fn_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · change sliceLin V n α' (factorAction 0 c d (ptE E d c F)) = factorAction 0 c d (ptE E d c (sliceLin V n α' F))
    rw [firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction]
  · simp

end U3Perm

section U3Succ
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem firstPositionSlice_positionAction_succ_apply (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' (factorAction k.succ a b F) β =
      (if (α' k).1 = a then F (Fin.cons (β 0) (Function.update α' k (b, (α' k).2))) else 0) -
      (if (α' k).2 = b then F (Fin.cons (β 0) (Function.update α' k ((α' k).1, a))) else 0) := by
  rw [firstPositionSlice_apply, factorAction_apply]
  simp only [Fin.cons_succ, ← Fin.cons_update]

theorem firstPositionSlice_positionAction_succ (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (factorAction k.succ a b F) =
      (if (α' k).1 = a then sliceLin V n (Function.update α' k (b, (α' k).2)) F else (0 : Arr V n 1)) -
      (if (α' k).2 = b then sliceLin V n (Function.update α' k ((α' k).1, a)) F else (0 : Arr V n 1)) := by
  refine indexArray_ext fun β => (firstPositionSlice_positionAction_succ_apply α' k a b F β).trans ?_
  have hf : ∀ X : Arr V n 1, X β =
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) β ∘ₗ arrOf V n 1) X :=
    fun X => rfl
  rw [hf, map_sub, ← hf, ← hf]
  congr 1
  · by_cases h1 : (α' k).1 = a
    · rw [if_pos h1, if_pos h1, firstPositionSlice_apply]
    · rw [if_neg h1, if_neg h1, hf, map_zero]
  · by_cases h2 : (α' k).2 = b
    · rw [if_pos h2, if_pos h2, firstPositionSlice_apply]
    · rw [if_neg h2, if_neg h2, hf, map_zero]

end U3Succ

section U3Stable
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem kStable_iSup_iSup {W : Type*} [AddCommGroup W] [Module ℂ W] (ε : Fin n → Bool)
    (T : Fin n → Fin n → Module.End ℂ W) {ι : Type*} {κ : ι → Prop} (S : ∀ i, κ i → Submodule ℂ W)
    (h : ∀ i k, KStable ε T (S i k)) : KStable ε T (⨆ i, ⨆ k, S i k) := by
  intro a b hab x hx
  have hle : (⨆ i, ⨆ k, S i k) ≤ Submodule.comap (T a b) (⨆ i, ⨆ k, S i k) := by
    refine iSup_le fun i => iSup_le fun k => ?_
    intro y hy
    exact (le_iSup_of_le i (le_iSup_of_le k le_rfl) : S i k ≤ ⨆ i, ⨆ k, S i k) (h i k a b hab y hy)
  exact hle hx

theorem raisingPart_invariant (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) : KStable ε (arrE E 1) (Vplus ε E Λ u) := by
  unfold Vplus isoPart
  exact kStable_iSup_iSup ε (arrE E 1) _ fun y _ => compactSpan_invariant ε (arrE E 1) y

theorem factorAction_mem_admissibleArrays {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (i : Fin j) {a b : Fin n} (hab : ε a = ε b) :
    factorAction i a b F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [factorAction_apply]
  by_cases hα : ∀ k, ε (α k).1 ≠ ε (α k).2
  · rw [if_pos hα]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact admissibleArrays_apply_mem hF _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact admissibleArrays_apply_mem hF _
      · exact Submodule.zero_mem _
  · rw [if_neg hα, Submodule.mem_bot]
    push_neg at hα
    obtain ⟨k, hk⟩ := hα
    have t1 : (if (α i).1 = a then F (Function.update α i (b, (α i).2)) else 0) = 0 := by
      split_ifs with h1
      · refine admissibleArrays_apply_eq_zero hF _ fun hall => ?_
        have hk' := hall k
        by_cases hki : k = i
        · rw [hki] at hk hk'
          simp at hk'
          exact hk' (by rw [← hab, ← h1, hk])
        · simp [Function.update_apply, hki] at hk'
          exact hk' hk
      · rfl
    have t2 : (if (α i).2 = b then F (Function.update α i ((α i).1, a)) else 0) = 0 := by
      split_ifs with h2
      · refine admissibleArrays_apply_eq_zero hF _ fun hall => ?_
        have hk' := hall k
        by_cases hki : k = i
        · rw [hki] at hk hk'
          simp at hk'
          exact hk' (by rw [hk, h2, hab])
        · simp [Function.update_apply, hki] at hk'
          exact hk' hk
      · rfl
    rw [t1, t2, sub_zero]

theorem pointwiseAction_mem_admissibleArrays {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) {a b : Fin n} (hab : ε a = ε b) :
    ptE E a b F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [pointwiseAction_apply]
  by_cases hα : ∀ k, ε (α k).1 ≠ ε (α k).2
  · rw [if_pos hα]
    exact compactSpan_invariant ε E u a b hab _ (admissibleArrays_apply_mem hF α)
  · rw [if_neg hα, Submodule.mem_bot, admissibleArrays_apply_eq_zero hF α hα, map_zero]

theorem admissibleArrays_invariant (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) :
    KStable ε (arrE E j) (arrV0 ε E u j) := by
  intro a b hab F hF
  first
    | simp only [arrE, LinearMap.add_apply, LinearMap.sum_apply]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_fn_sum, Finset.sum_apply]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => factorAction_mem_admissibleArrays hF i hab) (pointwiseAction_mem_admissibleArrays hF hab)

theorem firstPositionSlice_indexArrayAction (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (arrE E (j+1) a b F) = arrE E 1 a b (sliceLin V n α' F) +
      ∑ k : Fin j, sliceLin V n α' (factorAction k.succ a b F) := by
  first
    | simp only [arrE, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
    | simp only [arrE, LinearMap.add_apply, LinearMap.coe_fn_sum, Finset.sum_apply, map_add, map_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, firstPositionSlice_positionAction_zero, firstPositionSlice_pointwiseAction, add_zero]
  abel

theorem positiveArraysInvariant_holds : NStable := by
  intro V _ _ n ε E Λ u j a b hab F hF
  simp only [Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hF ⊢
  obtain ⟨⟨h0, hs⟩, hv⟩ := hF
  refine ⟨⟨admissibleArrays_invariant ε E u (j+1) a b hab F h0, ?_⟩, fun α' => ?_⟩
  · rw [mem_symmetricArrays] at hs ⊢
    intro σ
    have h1 : arrE E (j+1) a b (permArr V n σ F) = permArr V n σ (arrE E (j+1) a b F) :=
      LinearMap.congr_fun (indexArrayAction_mul_permutePositions E σ a b) F
    rw [← h1, hs σ]
  · rw [firstPositionSlice_indexArrayAction]
    refine Submodule.add_mem _ (raisingPart_invariant ε E Λ u a b hab _ (hv α'))
      (Submodule.sum_mem _ fun k _ => ?_)
    rw [firstPositionSlice_positionAction_succ]
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;> first | exact hv _ | exact Submodule.zero_mem _

end U3Stable

section U3Sym
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}

theorem inner_permutePositions (σ : Equiv.Perm (Fin j)) (F G : Arr V n j) :
    ⟪permArr V n σ F, permArr V n σ G⟫_ℂ = ⟪F, G⟫_ℂ := by
  rw [indexArray_inner, indexArray_inner]
  simp only [permutePositions_apply]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun α => rfl)

theorem inner_eq_sum_firstPositionSlice (F G : Arr V n (j+1)) :
    ⟪F, G⟫_ℂ = ∑ α' : Fin j → Fin n × Fin n, ⟪sliceLin V n α' F, sliceLin V n α' G⟫_ℂ := by
  rw [indexArray_inner, sum_fin_cons]
  simp only [indexArray_inner, firstPositionSlice_apply]

theorem symmetricSliceMixedCasimir_holds : OmSymSlice := by
  intro V _ _ n ε E j F
  refine ⟨fun hF i => ?_, ?_⟩
  · rw [mem_symmetricArrays] at hF
    have h1 : OmS ε E i (permArr V n (Equiv.swap 0 i) F) =
        permArr V n (Equiv.swap 0 i) (OmS ε E ((Equiv.swap 0 i).symm i) F) :=
      LinearMap.congr_fun (mixedCasimir_mul_permuteFactors ε E (Equiv.swap 0 i) i) F
    rw [hF, Equiv.symm_swap, Equiv.swap_apply_right] at h1
    rw [h1]
    calc _ = ⟪permArr V n (Equiv.swap 0 i) F, permArr V n (Equiv.swap 0 i) (OmS ε E 0 F)⟫_ℂ := by
          rw [hF]
      _ = _ := inner_permutePositions _ _ _
  · rw [inner_eq_sum_firstPositionSlice]
    simp only [firstPositionSlice_positionMixedCasimir_zero]

end U3Sym

section U3NPos
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}

theorem re_inner_self_indexArray (F : Arr V n j) : (⟪F, F⟫_ℂ).re = ‖F‖ ^ 2 := by
  first
    | exact inner_self_eq_norm_sq F
    | exact inner_self_eq_norm_sq (𝕜 := ℂ) F
    | simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F

theorem norm_sq_eq_sum_firstPositionSlice (F : Arr V n (j+1)) :
    ‖F‖ ^ 2 = ∑ α' : Fin j → Fin n × Fin n, ‖sliceLin V n α' F‖ ^ 2 := by
  rw [← re_inner_self_indexArray, inner_eq_sum_firstPositionSlice, Complex.re_sum]
  simp only [re_inner_self_indexArray]

end U3NPos

theorem nPos_of (hca : CasArr) (hs : OmSymSlice) (hp : OmPlus) : NPos := by
  intro V _ _ n ε E lam g u j hgl hu hk hfd hg F hF
  have hF' := hF
  simp only [Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hF'
  obtain ⟨⟨h0, hsym⟩, hv⟩ := hF'
  obtain ⟨h1, h2⟩ := hca V n ε E (LamOf ε lam) u (j+1)
  rw [h1 hgl hk F h0]
  have hsum : ∑ i : Fin (j+1), ⟪F, OmS ε E i F⟫_ℂ = ((j:ℂ) + 1) * ⟪F, OmS ε E 0 F⟫_ℂ := by
    calc ∑ i : Fin (j+1), ⟪F, OmS ε E i F⟫_ℂ = ∑ _i : Fin (j+1), ⟪F, OmS ε E 0 F⟫_ℂ :=
          Finset.sum_congr rfl fun i _ => (hs V n ε E j F).1 hsym i
      _ = _ := by
          first
            | simp
            | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring)
  have hom : (g - 2 * (n:ℝ)) * ‖F‖ ^ 2 ≤ (⟪F, OmS ε E 0 F⟫_ℂ).re := by
    rw [(hs V n ε E j F).2, Complex.re_sum, norm_sq_eq_sum_firstPositionSlice, Finset.mul_sum]
    exact Finset.sum_le_sum fun α' _ => hp V n ε E lam g u hgl hu hk hfd hg _ (hv α')
  have hpos := h2 F
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_sum, hsum]
  have e1 : (((ckv ε (LamOf ε lam) : ℝ) : ℂ) * ⟪F, F⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := by
    rw [Complex.re_ofReal_mul, re_inner_self_indexArray]
  have e2 : ((2:ℂ) * (((j:ℂ) + 1) * ⟪F, OmS ε E 0 F⟫_ℂ)).re =
      (2 * ((j:ℝ) + 1)) * (⟪F, OmS ε E 0 F⟫_ℂ).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [Complex.add_re, Complex.add_re, e1, e2]
  have h3 := mul_le_mul_of_nonneg_left hom (by positivity : (0:ℝ) ≤ 2 * ((j:ℝ) + 1))
  nlinarith [h3, hpos]

end Formalism.REAL
