import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}} (L : LB X)

def HasGen (F : (Y ⟶ X) →₀ ℤ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fsum φ ε = F ∧
    ∃ g : LB.Gen (LB.LinComb L φ ε), g.IsGen

variable {L}

lemma HasGen.of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (g : LB.Gen (LB.LinComb L φ ε))
    (hg : g.IsGen) : HasGen L (fsum φ ε) := ⟨K, inferInstance, φ, ε, rfl, g, hg⟩

lemma HasGen.gen (hL : L.IsLB) {F : (Y ⟶ X) →₀ ℤ} (h : HasGen L F) {K' : Type} [Fintype K']
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hF : fsum φ' ε' = F) : ∃ g : LB.Gen (LB.LinComb L φ' ε'), g.IsGen := by
  obtain ⟨K, _, φ, ε, hfs, g, hg⟩ := h
  obtain ⟨t', ht', -⟩ := gen_transport (L := L) hL ((sameSum_iff_fsum φ ε φ' ε').2 (hfs.trans hF.symm)) g hg
  exact ⟨t', ht'⟩

lemma HasGen.zero : HasGen L (0 : (Y ⟶ X) →₀ ℤ) := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ?_, ⟨fun _ => 1⟩, ?_⟩
  · simp [fsum]
  · intro i j
    have hg1 : (LB.LinComb L (Empty.elim : Empty → (Y ⟶ X)) Empty.elim).g i j = 1 :=
      by first
        | (dsimp only [LB.LinComb]; exact Fintype.prod_empty _)
        | (unfold LB.LinComb; exact Fintype.prod_empty _)
        | (simp [LB.LinComb]; rfl)
    dsimp only
    rw [MonoidHom.map_one, MonoidHom.map_one, hg1, one_mul]

lemma HasGen.add {F G : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (hG : HasGen L G) : HasGen L (F + G) := by
  have res_res : ∀ {Z : Scheme.{0}} {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Z, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro Z U V W h1 h2 x
    ext
    first
      | (simp only [res, Units.coe_map, MonoidHom.coe_coe]
         rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
         rfl)
      | (simp [res, ← Functor.map_comp_apply])
      | (simp [res]; rfl)
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  obtain ⟨K', _, φ', ε', rfl, g', hg'⟩ := hG
  have hl : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ (i ∘ Sum.inl) := by
    intro i x hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
  have hr : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ' (i ∘ Sum.inr) := by
    intro i x hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', ?_,
    ⟨fun i => res (hl i) (g.s (i ∘ Sum.inl)) * res (hr i) (g'.s (i ∘ Sum.inr))⟩, ?_⟩
  · simp [fsum, Fintype.sum_sum_type]
  · intro i j
    have hW : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
        LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) := inf_le_inf (hl i) (hl j)
    have hW' : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
        LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) := inf_le_inf (hr i) (hr j)
    have hGs : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
        res hW ((LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl)) *
          res hW' ((LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr)) := by
      first
        | (simp only [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow, res_res]; rfl)
        | (simp [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow]
           congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> erw [res_res] <;> try rfl)
        | (simp [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow]
           congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> rw [res_res])
    have e1 := congrArg (res hW) (hg (i ∘ Sum.inl) (j ∘ Sum.inl))
    have e2 := congrArg (res hW') (hg' (i ∘ Sum.inr) (j ∘ Sum.inr))
    erw [map_mul, res_res, res_res] at e1 e2
    dsimp only
    rw [hGs]
    erw [map_mul, map_mul, res_res, res_res, res_res, res_res, e1, e2]
    exact mul_mul_mul_comm _ _ _ _

lemma HasGen.neg {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : HasGen L (-F) := by
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  refine ⟨K, inferInstance, φ, fun k => -ε k, ?_, ⟨fun i => (g.s i)⁻¹⟩, ?_⟩
  · simp [fsum, Finsupp.single_neg, Finset.sum_neg_distrib]
  · intro i j
    have hgg : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
      first
        | (simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]; rfl)
        | (simp [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]; rfl)
        | (unfold LB.LinComb; simp [zpow_neg, Finset.prod_inv_distrib])
    have hij := hg i j
    dsimp only
    rw [hgg]
    exact (MonoidHom.map_inv _ _).trans <| (congrArg (fun x => x⁻¹) hij).trans <|
      (mul_inv _ _).trans <|
        congrArg (fun y => ((LB.LinComb L φ ε).g i j)⁻¹ * y) (MonoidHom.map_inv _ _).symm

lemma HasGen.sub {F G : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (hG : HasGen L G) : HasGen L (F - G) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma HasGen.nsmul {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : ∀ n : ℕ, HasGen L (n • F)
  | 0 => by rw [zero_smul]; exact HasGen.zero
  | n + 1 => by rw [add_smul, one_smul]; exact (hF.nsmul n).add hF

lemma HasGen.zsmul {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : ∀ n : ℤ, HasGen L (n • F)
  | (n : ℕ) => by rw [natCast_zsmul]; exact hF.nsmul n
  | Int.negSucc n => by rw [negSucc_zsmul]; exact (hF.nsmul (n + 1)).neg

lemma HasGen.pull {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (h : Z ⟶ Y) :
    HasGen L (Finsupp.mapDomain (fun ψ => h ≫ ψ) F) := by
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  exact ⟨K, inferInstance, fun k => h ≫ φ k, ε, fsum_comp φ ε h, LB.pullGen L φ ε g h,
    pullGen_isGen_of_isGen (L := L) φ ε g hg h⟩

end ReciprocityTheory.ChartRestriction.G.DVR
