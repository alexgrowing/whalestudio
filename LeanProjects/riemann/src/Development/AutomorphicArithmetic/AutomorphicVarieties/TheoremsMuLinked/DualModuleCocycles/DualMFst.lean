import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagAEntry
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TriAeval
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.FlagCUpMul
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_prod {A : Type} [CommRing A] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) A)
    (h1 : ∀ i a b, b < a → M i a b = 0) (h2 : ∀ i, M i i i = 0) : (List.ofFn M).prod = 0 := by
  have key : ∀ k, k ≤ n → ∀ a b : Fin n, b.val < k → ((List.ofFn M).take k).prod a b = 0 := by
    intro k
    induction k with
    | zero => intro _ a b hb; omega
    | succ k ih =>
      intro hk a b hb
      have hl : k < (List.ofFn M).length := by simp; omega
      rw [List.prod_take_succ _ _ hl, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val < k
      · rw [ih (by omega) a c hc, zero_mul]
      · have : (List.ofFn M)[k] c b = 0 := by
          rw [List.getElem_ofFn]
          by_cases hcb : b < c
          · exact h1 _ _ _ hcb
          · have hcb' : c.val ≤ b.val := not_lt.mp hcb
            have e1 : c = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            have e2 : b = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            rw [e1, e2]
            exact h2 _
        rw [this, mul_zero]
  ext a b
  have := key n le_rfl a b b.2
  rwa [List.take_of_length_le (by simp)] at this

private theorem kEl_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) (i : Fin n) :
    (kEl u α i).map f = kEl (u.map f) (fun j => f (α j)) i := by
  unfold kEl
  generalize Finset.univ.erase i = t
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, map_mul, map_mul, Matrix.map_mul, ih]
    congr 1
    ext a b
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]

private theorem kS_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kS u α).map f = kS (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kS, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem kT_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kT u α).map f = kT (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kT, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem fst_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.fst = A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem snd_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.snd =
      A.map TrivSqZeroExt.snd * B.map TrivSqZeroExt.fst + A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, ← Finset.sum_add_distrib, add_comm, mul_comm]

private theorem dualM_fst {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.fst = A := by
  ext a b
  simp [dualM]

private theorem dualM_snd {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.snd = B := by
  ext a b
  simp [dualM]

theorem UpperTheory.V.Th.Coc.flag :
    ∀ {O H : Type} [CommRing O] [IsDomain O] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) O) (ψ : Fin n → H → O) (s : H), (∀ g a b, b < a → r g a b = 0) → (∀ g i, r g i i = ψ i g) → (Function.Injective fun i => ψ i s) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (D : H → Matrix (Fin n) (Fin n) X) (a : Fin n → H → X), (∀ g : Fin n → H, (List.ofFn fun i => dualM (bar X (r (g i))) (D (g i)) - (TrivSqZeroExt.inl (algebraMap O X (ψ i (g i))) + TrivSqZeroExt.inr (a i (g i)) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ g, (∀ i j, j < i → (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i j = 0) ∧ ∀ i, (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i i = c₁ • a i g := by
  intro O H _ _ n r ψ s htri hdiag hinj
  have hrel : ∀ g : Fin n → H,
      (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) O)).prod = 0 := by
    intro g
    apply tri_prod
    · intro i a b hab
      simp [htri _ a b hab, Matrix.one_apply_ne hab.ne']
    · intro i
      simp [hdiag]
  obtain ⟨hoff, -⟩ := flagA r ψ s hrel
  obtain ⟨hB1, hB2⟩ := flagB (r s) (fun i => ψ i s) (htri s) (hdiag s)
  set S := kS (r s) (fun i => ψ i s) with hS
  set T := kT (r s) (fun i => ψ i s) with hT
  set Δ : Fin n → O := fun i => ∏ j ∈ Finset.univ.erase i, (ψ i s - ψ j s) with hΔ
  have hΔ0 : ∀ i, Δ i ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun j hj h => ?_
    exact (Finset.ne_of_mem_erase hj) (hinj (sub_eq_zero.mp h)).symm
  have hST : ∀ i, (S * T) i i = Δ i * Δ i := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hB2 i).1, (hB2 i).2]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [(hB1 i b h).1, zero_mul]
      · rw [(hB1 b i h).2, mul_zero]
    · simp
  obtain ⟨c₁, hc₁, hC⟩ := flagC S T Δ hΔ0 hB1 hB2 hoff
  refine ⟨c₁, hc₁, fun X _ _ D a hD => ?_⟩
  obtain ⟨h1, h2⟩ := flagA (fun g => dualM (bar X (r g)) (D g))
    (fun i g => (TrivSqZeroExt.inl (algebraMap O X (ψ i g)) + TrivSqZeroExt.inr (a i g) : DualNumber X)) s hD
  have eS := kS_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  have eT := kT_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  set S' := kS (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hS'
  set T' := kT (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hT'
  have hf : ⇑(TrivSqZeroExt.fstHom X X X).toRingHom = TrivSqZeroExt.fst := rfl
  have fS : S'.map TrivSqZeroExt.fst = bar X S := by
    rw [hf] at eS
    rw [eS, dualM_fst, hS, bar, bar, kS_map]
    simp
  have fT : T'.map TrivSqZeroExt.fst = bar X T := by
    rw [hf] at eT
    rw [eT, dualM_fst, hT, bar, bar, kT_map]
    simp
  have e1 : (S' * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X T + bar X S * T'.map TrivSqZeroExt.snd := by
    rw [snd_mul', fS, fT]
  have e2 : ∀ g, (S' * dualM (bar X (r g)) (D g) * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X (r g) * bar X T + bar X S * D g * bar X T +
        bar X S * bar X (r g) * T'.map TrivSqZeroExt.snd := by
    intro g
    rw [snd_mul', snd_mul', fst_mul', fS, fT, dualM_fst, dualM_snd, add_mul]
  have e3 : ∀ i, ((S' * T') i i).fst = algebraMap O X (Δ i * Δ i) := by
    intro i
    have : (S' * T').map TrivSqZeroExt.fst = bar X (S * T) := by
      rw [fst_mul', fS, fT, bar, bar, bar, Matrix.map_mul]
    have h := congrFun (congrFun this i) i
    rw [← hST]
    exact h
  obtain ⟨Y, hY⟩ := hC X (S'.map TrivSqZeroExt.snd) (T'.map TrivSqZeroExt.snd) (by
    intro a b hab
    rw [← e1, Matrix.map_apply, h1 a b hab, TrivSqZeroExt.snd_zero])
  refine ⟨Y, fun g => hY (r g) (D g) (fun i => a i g) (htri g) ?_ ?_⟩
  · intro i j hij
    rw [← e2, Matrix.map_apply, (h2 g).1 i j hij, TrivSqZeroExt.snd_zero]
  · intro i
    rw [← e2, ← e1, Matrix.map_apply, Matrix.map_apply, (h2 g).2 i, TrivSqZeroExt.snd_mul, e3, hdiag]
    generalize ((S' * T') i i).snd = z
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
