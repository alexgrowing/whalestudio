import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PhiAux

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem coord_apply' (k : ℕ) (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ F = F κ := rfl

theorem ofCoords_apply' {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := rfl

theorem wordContraction_apply (k : ℕ) (F : Big n k M) :
    phi E k F = ∑ κ, word E κ (F κ) := by
  first
  | simp only [phi, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.comp_apply, coord_apply']
  | (rw [phi, LinearMap.sum_apply]; rfl)
  | simp [phi, coord_apply']

theorem mAct_apply' (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply' (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) :
    factorAd (M := M) k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  first
  | (simp only [factorAd, ofCoords_apply', LinearMap.sub_apply]
     split_ifs <;> simp [coord_apply'])
  | (show ((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
        Big n k M →ₗ[ℂ] M) F = _
     split_ifs <;> simp [coord_apply'])

theorem rootWordProduct_zero (κ : Fin 0 → Fin n × Fin n) : word E κ = 1 := by
  first
  | rfl
  | simp [word]

theorem rootWordProduct_cons {k : ℕ} (p : Fin n × Fin n) (κ : Fin k → Fin n × Fin n) :
    word E (Fin.cons p κ : Fin (k + 1) → Fin n × Fin n) = E p.1 p.2 * word E κ := by
  first
  | simp only [word, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
  | simp [word, List.ofFn_succ]

theorem commutator_rootWordProduct (hE : IsGlRep E) (a b : Fin n) : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    E a b * word E κ - word E κ * E a b =
      ∑ i, ((if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) else 0) -
        (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) else 0))
  | 0, κ => by simp [rootWordProduct_zero]
  | k + 1, κ => by
    refine Fin.consCases (fun p τ => ?_) κ
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update,
      rootWordProduct_cons]
    have ih := commutator_rootWordProduct hE a b τ
    have h0 := hE a b p.1 p.2
    have hsplit : E a b * (E p.1 p.2 * word E τ) - E p.1 p.2 * word E τ * E a b =
        (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * word E τ +
          E p.1 p.2 * (E a b * word E τ - word E τ * E a b) := by noncomm_ring
    rw [hsplit, h0, ih, Finset.mul_sum]
    congr 1
    · have e1 : (b = p.1) = (p.1 = b) := propext eq_comm
      simp only [e1]
      split_ifs <;> simp [sub_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [mul_sub]

theorem sum_ite_update_reindex {k : ℕ} (i : Fin k) (P Q : Fin n × Fin n → Prop) [DecidablePred P]
    [DecidablePred Q] (f g : Fin n × Fin n → Fin n × Fin n) (hf : ∀ p, P p → Q (f p))
    (hg : ∀ p, Q p → P (g p)) (hgf : ∀ p, P p → g (f p) = p) (hfg : ∀ p, Q p → f (g p) = p)
    (W : (Fin k → Fin n × Fin n) → Module.End ℂ M) (F : Big n k M) :
    ∑ κ, (if P (κ i) then W κ (F (Function.update κ i (f (κ i)))) else 0) =
      ∑ κ, (if Q (κ i) then W (Function.update κ i (g (κ i))) (F κ) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun κ => Function.update κ i (f (κ i)))
    (fun κ => Function.update κ i (g (κ i))) ?_ ?_ ?_ ?_ ?_ <;>
  intro κ hκ <;>
  simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
    Finset.mem_univ, true_and] at hκ ⊢
  · simpa using hf _ hκ
  · simpa using hg _ hκ
  · simp [hgf _ hκ]
  · simp [hfg _ hκ]
  · simp [hgf _ hκ]

theorem positionTensorAction_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    bAct E k a b F κ = E a b (F κ) + ∑ i, factorAd (M := M) k i a b F κ := by
  rw [← coord_apply' k κ (bAct E k a b F)]
  first
  | (simp only [bAct, LinearMap.add_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_add, map_sum]
     simp only [coord_apply', mAct_apply'])
  | (simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
     simp only [coord_apply', mAct_apply'])

private theorem linearMap_apply_ite_zero (T : Module.End ℂ M) (c : Prop) [Decidable c] (x : M) :
    T (if c then x else 0) = if c then T x else 0 := by
  split_ifs <;> simp

private theorem ite_linearMap_zero_apply (T : Module.End ℂ M) (c : Prop) [Decidable c] (x : M) :
    (if c then T else 0) x = if c then T x else 0 := by
  split_ifs <;> simp

theorem wordContraction_tensorAction (hE : IsGlRep E) (k : ℕ) (a b : Fin n) (F : Big n k M) :
    phi E k (bAct E k a b F) = E a b (phi E k F) := by
  have h1 : ∀ i : Fin k, ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).1 = a then word E κ (F (Function.update κ i (b, (κ i).2))) else 0) =
      ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) (F κ) else 0) := fun i =>
    sum_ite_update_reindex i (fun p => p.1 = a) (fun p => p.1 = b) (fun p => (b, p.2)) (fun p => (a, p.2))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun p hp => Prod.ext hp.symm rfl)
      (fun p hp => Prod.ext hp.symm rfl) (fun κ => word E κ) F
  have h2 : ∀ i : Fin k, ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).2 = b then word E κ (F (Function.update κ i ((κ i).1, a))) else 0) =
      ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) (F κ) else 0) := fun i =>
    sum_ite_update_reindex i (fun p => p.2 = b) (fun p => p.2 = a) (fun p => (p.1, a)) (fun p => (p.1, b))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun p hp => Prod.ext rfl hp.symm)
      (fun p hp => Prod.ext rfl hp.symm) (fun κ => word E κ) F
  have hc : ∀ κ : Fin k → Fin n × Fin n, E a b (word E κ (F κ)) = word E κ (E a b (F κ)) +
      ∑ i, ((if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) (F κ) else 0) -
        (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) (F κ) else 0)) := by
    intro κ
    have h := congrArg (fun T : Module.End ℂ M => T (F κ)) (commutator_rootWordProduct hE a b κ)
    first
    | simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
        ite_linearMap_zero_apply] at h
    | simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
        ite_linearMap_zero_apply] at h
    first
    | exact sub_eq_iff_eq_add'.mp h
    | (rw [← h]; abel)
  rw [wordContraction_apply, wordContraction_apply, map_sum]
  simp only [positionTensorAction_apply, factorAd_apply', map_add, map_sum, map_sub,
    linearMap_apply_ite_zero, hc, Finset.sum_add_distrib]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1 i, h2 i]

theorem apply_mem_noncompactLayer_succ {k : ℕ} {a b : Fin n} (hab : ε a ≠ ε b) {w : M}
    (hw : w ∈ layer ε E V k) : E a b w ∈ layer ε E V (k + 1) := by
  show E a b w ∈ layer ε E V k ⊔
    ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
  refine Submodule.mem_sup_right ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem hab (Submodule.mem_map_of_mem hw)))

theorem rootWordProduct_mem_noncompactLayer : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    (∀ i, ε (κ i).1 ≠ ε (κ i).2) → ∀ v ∈ V, word E κ v ∈ layer ε E V k
  | 0, κ, _, v, hv => by rw [rootWordProduct_zero]; exact hv
  | k + 1, κ, hκ, v, hv => by
    revert hκ
    refine Fin.consCases (fun p τ => ?_) κ
    intro hκ
    rw [rootWordProduct_cons, Module.End.mul_apply]
    have hp : ε p.1 ≠ ε p.2 := by simpa using hκ 0
    have hτ : ∀ i, ε (τ i).1 ≠ ε (τ i).2 := fun i => by simpa using hκ i.succ
    exact apply_mem_noncompactLayer_succ hp (rootWordProduct_mem_noncompactLayer τ hτ v hv)

theorem mem_noncompactPositionSubmodule_iff' {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ, F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  first
  | (rw [ncV, Submodule.mem_iInf]; rfl)
  | simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap, coord_apply']

theorem wordContraction_mem_noncompactLayer' {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) :
    phi E k F ∈ layer ε E V k := by
  rw [wordContraction_apply]
  refine Submodule.sum_mem _ fun κ _ => ?_
  have h := mem_noncompactPositionSubmodule_iff'.mp hF κ
  split_ifs at h with hκ
  · exact rootWordProduct_mem_noncompactLayer κ hκ _ h
  · rw [Submodule.mem_bot] at h
    rw [h, map_zero]
    exact Submodule.zero_mem _

def indexPairPrepend {k : ℕ} (p : Fin n × Fin n) (G : Big n k M) : Big n (k + 1) M :=
  WithLp.toLp 2 (fun κ : Fin (k + 1) → Fin n × Fin n => if κ 0 = p then G (Fin.tail κ) else 0)

theorem wordContraction_prepend {k : ℕ} (p : Fin n × Fin n) (G : Big n k M) :
    phi E (k + 1) (indexPairPrepend p G) = E p.1 p.2 (phi E k G) := by
  rw [wordContraction_apply, wordContraction_apply, map_sum]
  have hL : ∀ κ : Fin (k + 1) → Fin n × Fin n, word E κ ((indexPairPrepend p G) κ) =
      if κ 0 = p then word E κ (G (Fin.tail κ)) else 0 := by
    intro κ
    show word E κ (if κ 0 = p then G (Fin.tail κ) else 0) = _
    split_ifs <;> simp
  simp_rw [hL]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun κ => Fin.tail κ) (fun κ' => Fin.cons p κ') ?_ ?_ ?_ ?_ ?_ <;>
  intro κ hκ <;>
  simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
    Finset.mem_univ, true_and] at hκ ⊢
  · simp
  · rw [← hκ]; exact Fin.cons_self_tail κ
  · exact Fin.tail_cons _ _
  · have e : κ = Fin.cons p (Fin.tail κ) := by
      rw [← hκ]; exact (Fin.cons_self_tail κ).symm
    calc word E κ (G (Fin.tail κ))
        = word E (Fin.cons p (Fin.tail κ) : Fin (k + 1) → Fin n × Fin n) (G (Fin.tail κ)) := by
          rw [← e]
      _ = _ := by rw [rootWordProduct_cons]; rfl

theorem positionPrepend_mem_noncompactPositionSubmodule {k : ℕ} {p : Fin n × Fin n} (hp : ε p.1 ≠ ε p.2) {G : Big n k M}
    (hG : G ∈ ncV ε V k) : indexPairPrepend p G ∈ ncV ε V (k + 1) := by
  rw [mem_noncompactPositionSubmodule_iff'] at hG ⊢
  intro κ
  by_cases h0 : κ 0 = p
  · have hv : (indexPairPrepend p G) κ = G (Fin.tail κ) := by
      show (if κ 0 = p then G (Fin.tail κ) else 0) = _
      rw [if_pos h0]
    rw [hv]
    have h := hG (Fin.tail κ)
    by_cases ht : ∀ i, ε (Fin.tail κ i).1 ≠ ε (Fin.tail κ i).2
    · rw [if_pos ht] at h
      have hk : ∀ i, ε (κ i).1 ≠ ε (κ i).2 := by
        intro i
        induction i using Fin.cases with
        | zero => rw [h0]; exact hp
        | succ j => exact ht j
      rw [if_pos hk]; exact h
    · rw [if_neg ht, Submodule.mem_bot] at h
      rw [h]; exact Submodule.zero_mem _
  · have hv : (indexPairPrepend p G) κ = 0 := by
      show (if κ 0 = p then G (Fin.tail κ) else 0) = _
      rw [if_neg h0]
    rw [hv]; exact Submodule.zero_mem _

theorem map_noncompactLayer_le_sup : ∀ (k : ℕ) (a b : Fin n), ε a ≠ ε b →
    (layer ε E V k).map (E a b) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1))
  | 0, a, b, hab => by
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_comap]
    refine Submodule.mem_sup_right ?_
    let G : Big n 0 M := WithLp.toLp 2 (fun _ => v)
    have hG : G ∈ ncV ε V 0 := by
      rw [mem_noncompactPositionSubmodule_iff']; intro κ
      rw [if_pos (fun i => i.elim0)]; exact hv
    have hphi : phi E 0 G = v := by
      rw [wordContraction_apply]; simp [G, rootWordProduct_zero]
    refine ⟨indexPairPrepend (a, b) G, positionPrepend_mem_noncompactPositionSubmodule hab hG, ?_⟩
    rw [wordContraction_prepend, hphi]
  | k + 1, a, b, hab => by
    rw [Submodule.map_le_iff_le_comap]
    simp only [layer]
    refine sup_le ?_ (iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_)
    · intro w hw
      exact Submodule.mem_sup_left (apply_mem_noncompactLayer_succ hab hw)
    · rw [Submodule.map_le_iff_le_comap]
      intro w hw
      simp only [Submodule.mem_comap]
      have h1 := map_noncompactLayer_le_sup k c d hcd (Submodule.mem_map_of_mem hw)
      obtain ⟨u, hu, y, ⟨G, hG, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
      rw [← hsum, map_add]
      refine add_mem (Submodule.mem_sup_left (apply_mem_noncompactLayer_succ hab hu))
        (Submodule.mem_sup_right ⟨indexPairPrepend (a, b) G, positionPrepend_mem_noncompactPositionSubmodule hab hG, ?_⟩)
      rw [wordContraction_prepend]

theorem noncompactLayer_succ_le_sup' (k : ℕ) :
    layer ε E V (k + 1) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1)) := by
  show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
  exact sup_le le_sup_left (iSup_le fun a => iSup_le fun b => iSup_le fun hab => map_noncompactLayer_le_sup k a b hab)

end PhiAux

section Phi

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem phi_bAct (hE : IsGlRep E) (k : ℕ) {a b : Fin n} (hab : ε a = ε b) (F : Big n k M) :
    phi E k (bAct E k a b F) = E a b (phi E k F) := wordContraction_tensorAction hE k a b F

theorem phi_mem_layer {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) :
    phi E k F ∈ layer ε E V k := wordContraction_mem_noncompactLayer' hF

theorem layer_succ_le (hE : IsGlRep E) (hV : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V (k + 1) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1)) := noncompactLayer_succ_le_sup' k

end Phi

end ReciprocityTheory.ChartRestriction.DS
