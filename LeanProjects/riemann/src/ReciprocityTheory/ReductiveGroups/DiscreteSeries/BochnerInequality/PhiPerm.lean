import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PhiPerm

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem mem_ncV_iff_apply {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem phi_apply_eq (k : ℕ) (F : Big n k M) : phi E k F = ∑ κ, word E κ (F κ) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

theorem permute_mem_ncV {k : ℕ} (σ : Equiv.Perm (Fin k)) {F : Big n k M} (hF : F ∈ ncV ε V k) :
    permute σ F ∈ ncV ε V k := by
  rw [mem_ncV_iff_apply] at hF ⊢
  intro κ
  rw [permute_apply]
  have hκ := hF (κ ∘ σ)
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · have hc' : ∀ i, ε ((κ ∘ σ) i).1 ≠ ε ((κ ∘ σ) i).2 := fun i => hc (σ i)
    rw [if_pos hc'] at hκ
    rw [if_pos hc]
    exact hκ
  · have hc' : ¬ ∀ i, ε ((κ ∘ σ) i).1 ≠ ε ((κ ∘ σ) i).2 := fun h => hc (fun i => by
      have := h (σ.symm i)
      simpa using this)
    rw [if_neg hc'] at hκ
    rw [if_neg hc]
    exact hκ

theorem bool_eq_of_ne_ne {x y z : Bool} (h1 : x ≠ y) (h2 : y ≠ z) : x = z := by
  cases x <;> cases y <;> cases z <;> simp_all

theorem listProd_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    (l : List (Fin n × Fin n)) {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) :
    (l.map fun p => E p.1 p.2).prod v ∈ layer ε E V (j + l.length) := by
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact apply_mem_layer_succ hE hV p.1 p.2 ih

theorem listProd_perm_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) (hnc : ∀ p ∈ l₁, ε p.1 ≠ ε p.2)
    {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) (m : ℕ) (hm : l₁.length ≤ m + 1) :
    (l₁.map fun p => E p.1 p.2).prod v - (l₂.map fun p => E p.1 p.2).prod v ∈
      layer ε E V (j + m) := by
  induction hp generalizing m with
  | nil => simp
  | @cons x l₁ l₂ h ih =>
    rcases m with _ | m
    · have hl1 : l₁ = [] := by simpa using hm
      subst hl1
      have hl2 := List.Perm.nil_eq h
      subst hl2
      simp
    · have hD := ih (fun p hp' => hnc p (List.mem_cons_of_mem _ hp')) m (by simpa using hm)
      have := apply_mem_layer_succ hE hV x.1 x.2 hD
      rw [map_sub] at this
      simpa [List.map_cons, List.prod_cons, Module.End.mul_apply, add_assoc] using this
  | swap x y l =>
    have hw := listProd_mem_layer hE hV l hv
    have hlen : j + l.length + 1 ≤ j + m := by simp at hm; omega
    have h1 : ∀ a b, (E a b) ((l.map fun p => E p.1 p.2).prod v) ∈ layer ε E V (j + m) :=
      fun a b => layer_mono hlen (apply_mem_layer_succ hE hV a b hw)
    have key : ((y :: x :: l).map fun p => E p.1 p.2).prod v - ((x :: y :: l).map fun p => E p.1 p.2).prod v =
        (E y.1 y.2 * E x.1 x.2 - E x.1 x.2 * E y.1 y.2) ((l.map fun p => E p.1 p.2).prod v) := by
      simp only [List.map_cons, List.prod_cons, LinearMap.sub_apply, Module.End.mul_apply]
    rw [key, hE, LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact h1 _ _
      · simp
    · split_ifs
      · exact h1 _ _
      · simp
  | trans h₁ h₂ ih₁ ih₂ =>
    have hA := ih₁ hnc m hm
    have hB := ih₂ (fun p hp' => hnc p (h₁.symm.subset hp')) m (by rw [← h₁.length_eq]; exact hm)
    have := Submodule.add_mem _ hA hB
    rwa [sub_add_sub_cancel] at this

theorem word_eq_listProd {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    word E κ = ((List.ofFn κ).map fun p => E p.1 p.2).prod := by
  rw [word, List.map_ofFn]
  rfl

theorem phi_permute_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V) {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) {F : Big n (k + 1) M} (hF : F ∈ ncV ε V (k + 1)) :
    phi E (k + 1) F - phi E (k + 1) (permute σ F) ∈ layer ε E V k := by
  rw [phi_apply_eq, phi_apply_eq]
  have hre : ∑ κ, word E κ ((permute σ F) κ) = ∑ κ, word E (κ ∘ σ.symm) (F κ) := by
    let e : (Fin (k + 1) → Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
      ⟨fun κ => κ ∘ σ, fun κ => κ ∘ σ.symm, fun κ => by funext i; simp, fun κ => by funext i; simp⟩
    refine Fintype.sum_equiv e _ _ (fun κ => ?_)
    show word E κ (permute σ F κ) = word E ((κ ∘ σ) ∘ σ.symm) (F (κ ∘ σ))
    have hκ : (κ ∘ σ) ∘ σ.symm = κ := by funext i; simp
    rw [hκ, permute_apply]
  rw [hre, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun κ _ => ?_)
  have hFκ := (mem_ncV_iff_apply.1 hF) κ
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · rw [if_pos hc] at hFκ
    rw [word_eq_listProd, word_eq_listProd]
    have hp : (List.ofFn κ).Perm (List.ofFn (κ ∘ σ.symm)) := (Equiv.Perm.ofFn_comp_perm σ.symm κ).symm
    have hnc : ∀ p ∈ List.ofFn κ, ε p.1 ≠ ε p.2 := fun p hp' => by
      rw [List.mem_ofFn] at hp'
      obtain ⟨i, rfl⟩ := hp'
      exact hc i
    have := listProd_perm_sub_mem hE hV hp hnc (show F κ ∈ layer ε E V 0 from hFκ) k (by simp)
    rw [zero_add] at this
    exact this
  · rw [if_neg hc] at hFκ
    rw [(Submodule.mem_bot ℂ).1 hFκ]
    simp

end PhiPerm

end ReciprocityTheory.ChartRestriction.DS
