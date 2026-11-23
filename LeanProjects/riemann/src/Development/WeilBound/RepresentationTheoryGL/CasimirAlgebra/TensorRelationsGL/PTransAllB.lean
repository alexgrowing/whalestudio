import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllA

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]

def merge (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) : P → Fin n :=
  fun p => if h : q p then J ⟨p, h⟩ else I ⟨p, h⟩

omit [Fintype P] [DecidableEq P] in
theorem merge_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) :
    merge q J I x.1 = J x := by simp [merge, x.2]

omit [Fintype P] [DecidableEq P] in
theorem merge_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) :
    merge q J I x.1 = I x := by simp [merge, x.2]

omit [Fintype P] in
theorem merge_upd_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) (c : Fin n) :
    merge q (Function.update J x c) I = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]
  · have hp : p ≠ x.1 := fun e => h (e ▸ x.2)
    simp [merge, h, hp]

omit [Fintype P] in
theorem merge_upd_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · have hp : p ≠ x.1 := fun e => x.2 (e ▸ h)
    simp [merge, h, hp]
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // ¬ q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]

def spl : TV n M P ≃ₗ[ℂ] TV n (TV n M {p // ¬ q p}) {p // q p} where
  toFun F J I := F (merge q J I)
  invFun G K := G (fun x => K x.1) (fun x => K x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    funext K
    show F (merge q _ _) = F K
    congr 1
    funext p
    by_cases h : q p <;> simp [merge, h]
  right_inv G := by
    funext J I
    show G (fun x => merge q J I x.1) (fun x => merge q J I x.1) = G J I
    congr 1 <;> funext x
    · exact merge_left q J I x
    · exact merge_right q J I x

omit [Fintype P] [DecidableEq P] in
theorem spl_apply (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := rfl

omit [Fintype P] in
theorem spl_tE (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by
  funext J I
  simp only [spl_apply, tE, lift, eAt, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not S q, add_comm]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : I x = a
    · simp [h, merge_right, spl_apply, merge_upd_right]
    · simp [h, merge_right]
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J x = a
    · simp [h, merge_left, spl_apply, merge_upd_left]
    · simp [h, merge_left]

omit [DecidableEq P] in
theorem card_sub (r : P → Prop) [DecidablePred r] :
    (Finset.univ.filter fun x : {p // q p} => r x.1).card = (Finset.univ.filter fun p => q p ∧ r p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype q)]
  congr 1
  ext p
  simp [and_comm]

private theorem subtypePerm_subtypeCongr_eq {q : P → Prop} [DecidablePred q] (σ : Equiv.Perm P)
    (h0 : ∀ x, q (σ x) ↔ q x) (h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x) :
    (σ.subtypePerm h0).subtypeCongr (σ.subtypePerm (p := fun x => ¬ q x) h1) = σ := by
  ext x
  by_cases hx : q x
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem cA_split {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by
  simp only [cA, alt, colG, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, map_sum, map_smul, pm, LinearMap.pi_apply]
  simp_rw [Finset.smul_sum, smul_smul, spl_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun τ _ => τ.1.subtypeCongr τ.2) ?_ ?_ ?_ ?_
  · rintro ⟨σ0, σ1⟩ hτ
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    intro x
    by_cases hx : q x
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      exact hτ.1 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      exact hτ.2 ⟨x, hx⟩
  · rintro ⟨σ0, σ1⟩ _ ⟨σ0', σ1'⟩ _ he
    simp only at he
    have e0 : σ0 = σ0' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.left_apply _ _ x.2] at this
      exact this
    have e1 : σ1 = σ1' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.right_apply _ _ x.2] at this
      exact this
    rw [e0, e1]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have h0 : ∀ x, q (σ x) ↔ q x := fun x => hq _ _ (hσ x)
    have h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x := fun x => not_congr (h0 x)
    refine ⟨(σ.subtypePerm h0, σ.subtypePerm (p := fun x => ¬ q x) h1), ?_, subtypePerm_subtypeCongr_eq σ h0 h1⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun x => hσ x.1, fun x => hσ x.1⟩
  · rintro ⟨σ0, σ1⟩ _
    simp only
    rw [Equiv.Perm.sign_subtypeCongr]
    congr 1
    · push_cast
      ring
    · congr 1
      funext x
      by_cases hx : q x
      · simp [merge, hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      · simp [merge, hx, Equiv.Perm.subtypeCongr.right_apply _ _ hx]

end PositivityTheory.Rg.Cz.TA

end
