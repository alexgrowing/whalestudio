import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanStep
variable {T : Type 1} [Category.{0} T]

abbrev altCx (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) : CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

theorem alternatingCofaceComplexOfFunctor_d_zero_one (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 0 1 y = F.map (X.δ (n := 0) 0) y - F.map (X.δ (n := 0) 1) y := by
  have h0 : (altCx X F).d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F) 0 :=
    CochainComplex.of_d (fun n ↦ (X ⋙ F).obj (SimplexCategory.mk n)) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F)) 0
  rw [h0]
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg, CosimplicialObject.δ]
  rfl

theorem altCx_nat (X : CosimplicialObject T) {F G : T ⥤ AddCommGrpCat.{1}} (φ : F ⟶ G) (n m : ℕ)
    (w : F.obj (X.obj (SimplexCategory.mk n))) :
    (altCx X G).d n m (φ.app _ w) = φ.app _ ((altCx X F).d n m w) := by
  have h := ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerLeft X φ)).comm n m
  exact ConcreteCategory.congr_hom h w

theorem altCx_dd (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 1 2 ((altCx X F).d 0 1 y) = 0 :=
  ConcreteCategory.congr_hom ((altCx X F).d_comp_d 0 1 2) y

theorem altCx_exact1 (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (h : (altCx X F).ExactAt 1)
    (w : F.obj (X.obj (SimplexCategory.mk 1))) (hw : (altCx X F).d 1 2 w = 0) :
    ∃ v : F.obj (X.obj (SimplexCategory.mk 0)), (altCx X F).d 0 1 v = w := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem aug_δ {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) (j : Fin 2) :
    a.app (SimplexCategory.mk 0) ≫ X.δ j = a.app (SimplexCategory.mk 1) := by
  have h := a.naturality (SimplexCategory.δ j)
  simpa [CosimplicialObject.δ] using h.symm

theorem cartan_step : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (Z M N : T ⥤ AddCommGrpCat.{1}) (i : Z ⟶ M) (d : M ⟶ N), (∀ V, Function.Injective (i.app V)) → (∀ V (y : M.obj V), d.app V y = 0 ↔ ∃ w, i.app V w = y) → WExact M a → WExact N a → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ Z)).ExactAt 1 → ∀ (z : N.obj U) (y : M.obj (X.obj (SimplexCategory.mk (0)))), d.app _ y = N.map (a.app (SimplexCategory.mk (0))) z → ∃ x : M.obj U, d.app U x = z := by
  intro T _ U X a Z M N i d hi hd hM hN hZ z y hy
  have hu : d.app _ ((altCx X M).d 0 1 y) = 0 := by
    rw [alternatingCofaceComplexOfFunctor_d_zero_one, map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hy,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← N.map_comp, ← N.map_comp,
      aug_δ a 0, aug_δ a 1, sub_self]
  obtain ⟨w, hw⟩ := (hd _ _).1 hu
  have hw2 : (altCx X Z).d 1 2 w = 0 := by
    have h1 : i.app _ ((altCx X Z).d 1 2 w) = 0 := by
      rw [← altCx_nat X i 1 2 w, hw, altCx_dd]
      rfl
    exact hi _ (h1.trans (map_zero _).symm)
  obtain ⟨v, hv⟩ := altCx_exact1 X Z hZ w hw2
  have hy' : M.map (X.δ (n := 0) 0) (y - i.app _ v) = M.map (X.δ (n := 0) 1) (y - i.app _ v) := by
    rw [← sub_eq_zero, map_sub, map_sub, sub_sub_sub_comm, ← alternatingCofaceComplexOfFunctor_d_zero_one, ← alternatingCofaceComplexOfFunctor_d_zero_one, altCx_nat X i 0 1, hv, hw]
    exact sub_self _
  obtain ⟨x, hx⟩ := hM.2.1 _ hy'
  refine ⟨x, hN.1 ?_⟩
  have e := ConcreteCategory.congr_hom (d.naturality (a.app (SimplexCategory.mk 0))) x
  simp only [ConcreteCategory.comp_apply] at e
  have e2 : d.app (X.obj (SimplexCategory.mk 0)) (y - i.app _ v) = N.map (a.app (SimplexCategory.mk 0)) z := by
    rw [map_sub, hy, (hd _ _).2 ⟨v, rfl⟩, sub_zero]
  rw [← hx] at e2
  exact e.symm.trans e2

end GlobalTheory.CartanStep
