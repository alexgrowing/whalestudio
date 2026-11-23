import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

lemma pullU_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  ext
  simp only [pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app]
  rfl

set_option maxHeartbeats 1000000 in
lemma pullback_generator_isGenerator {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Z ⟶ Y) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
        (LB.LinComb L (fun k => h ≫ φ k) ε).U i) ((LB.pullGen L φ ε t h).s i) =
      (LB.LinComb L (fun k => h ≫ φ k) ε).g i j *
        res (inf_le_right : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
          (LB.LinComb L (fun k => h ≫ φ k) ε).U j) ((LB.pullGen L φ ε t h).s j) := by
  have hW : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
      h ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 k⟩
  have h1 := congrArg (fun z : Γ(Y, ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j))ˣ =>
    res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) z)) (ht i j)
  simp only [map_mul, pullU_res, res_res'] at h1
  have e0 : (LB.LinComb L φ ε).g i j = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)) :
        ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
      (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k) := rfl
  have e1 : (LB.LinComb L (fun k => h ≫ φ k) ε).g i j = ∏ k, (res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)
      (res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)) :
        ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
      (pullU (φ k) _ (L.g (i k) (j k)))))) ^ (ε k) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    erw [pullU_res, res_res']
    try rfl
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K → Γ(Y, ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j))ˣ, (LB.LinComb L φ ε).g i j = ∏ k, a k ^ ε k ∧
      (LB.LinComb L (fun k => h ≫ φ k) ε).g i j = ∏ k, (res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) (a k))) ^ ε k :=
    ⟨_, e0, e1⟩
  have hg : (LB.LinComb L (fun k => h ≫ φ k) ε).g i j =
      res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ((LB.LinComb L φ ε).g i j)) := by
    rw [ha1, ha0]
    first
      | (rw [map_prod, map_prod]; exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow])
      | simp only [map_prod, map_zpow]
  rw [hg]
  erw [res_res', res_res']
  exact h1

theorem pullGen_isGen {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Z ⟶ Y) : (LB.pullGen L φ ε t h).IsGen := fun i j => pullback_generator_isGenerator L φ ε t ht h i j

lemma inverse_generator_isGenerator {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
        (LB.LinComb L φ (fun k => -ε k)).U i) ((LB.invGen L φ ε t).s i) =
      (LB.LinComb L φ (fun k => -ε k)).g i j *
        res (inf_le_right : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
          (LB.LinComb L φ (fun k => -ε k)).U j) ((LB.invGen L φ ε t).s j) := by
  have h1 := ht i j
  have hg : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
    (simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]) <;> rfl
  have h2 := congrArg (fun z => z⁻¹) h1
  simp only [mul_inv, ← map_inv] at h2
  rw [hg]
  exact h2

theorem invGen_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : (LB.invGen L φ ε t).IsGen := fun i j => inverse_generator_isGenerator L φ ε t ht i j

set_option maxHeartbeats 1000000 in
lemma product_generator_isGenerator {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen)
    (i j : K ⊕ K' → L.ι) :
    res (inf_le_left : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
        (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i)
        ((LB.mulGen L φ ε φ' ε' t t').s i) =
      (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j *
        res (inf_le_right : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
          (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j)
          ((LB.mulGen L φ ε φ' ε' t t').s j) := by
  have hA : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤
      (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 (Sum.inl k)⟩
  have hB : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤
      (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 (Sum.inr k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 (Sum.inr k)⟩
  have hg : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
      res hA ((LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl)) *
        res hB ((LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr)) := by
    have e0 : (LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl) = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ (i ∘ Sum.inl) k))
      (inf_le_right.trans (LB.wchart_le L φ (j ∘ Sum.inl) k)) :
        (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
      (pullU (φ k) _ (L.g (i (Sum.inl k)) (j (Sum.inl k))))) ^ (ε k) := rfl
    have e0' : (LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr) = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ' (i ∘ Sum.inr) k))
      (inf_le_right.trans (LB.wchart_le L φ' (j ∘ Sum.inr) k)) :
        (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
      (pullU (φ' k) _ (L.g (i (Sum.inr k)) (j (Sum.inr k))))) ^ (ε' k) := rfl
    have e1 : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
        (∏ k, (res hA (res (le_inf (inf_le_left.trans (LB.wchart_le L φ (i ∘ Sum.inl) k))
      (inf_le_right.trans (LB.wchart_le L φ (j ∘ Sum.inl) k)) :
        (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
      (pullU (φ k) _ (L.g (i (Sum.inl k)) (j (Sum.inl k)))))) ^ (ε k)) *
          ∏ k, (res hB (res (le_inf (inf_le_left.trans (LB.wchart_le L φ' (i ∘ Sum.inr) k))
      (inf_le_right.trans (LB.wchart_le L φ' (j ∘ Sum.inr) k)) :
        (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
      (pullU (φ' k) _ (L.g (i (Sum.inr k)) (j (Sum.inr k)))))) ^ (ε' k) := by
      refine (Fintype.prod_sum_type _).trans ?_
      congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> congr 1 <;> erw [res_res'] <;> rfl
    obtain ⟨a, a', ha, ha', hb⟩ : ∃ (a : K → Γ(Y, ((LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl)))ˣ) (a' : K' → Γ(Y, ((LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr)))ˣ),
        (LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl) = ∏ k, a k ^ ε k ∧
        (LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr) = ∏ k, a' k ^ ε' k ∧
        (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
          (∏ k, (res hA (a k)) ^ ε k) * ∏ k, (res hB (a' k)) ^ ε' k := ⟨_, _, e0, e0', e1⟩
    rw [hb, ha, ha']
    first
      | (rw [map_prod, map_prod]
         congr 1 <;> exact Finset.prod_congr rfl fun k _ => by rw [map_zpow])
      | simp only [map_prod, map_zpow]
  have h1 := congrArg (fun z : Γ(Y, (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl))ˣ =>
    res hA z) (ht (i ∘ Sum.inl) (j ∘ Sum.inl))
  have h2 := congrArg (fun z : Γ(Y, (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr))ˣ =>
    res hB z) (ht' (i ∘ Sum.inr) (j ∘ Sum.inr))
  simp only [map_mul, res_res'] at h1 h2
  rw [hg]
  erw [map_mul, map_mul]
  erw [res_res', res_res', res_res', res_res']
  rw [mul_mul_mul_comm (res hA _) (res hB _)]
  erw [h1, h2]
  try rfl

theorem mulGen_isGen {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := fun i j => product_generator_isGenerator L φ ε φ' ε' t t' ht ht' i j

end ReciprocityTheory.ChartRestriction.G.DVR
