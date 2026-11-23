import Development.EtaleCohomology.EtaleSheaves.EtaleGroupHomologySlantOfDeltaCochain

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

theorem slantHom_neg (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} :
    ∃ f : ((Fin m → Γ) →₀ R) →+ _, ∀ c, f c = slantHom R X c :=
  ⟨AddMonoidHom.mk' (slantHom R X) (slantHom_add R X), fun _ => rfl⟩

theorem homD_of (h : Faces) : HomD := by
  intro R _ Γ _ X m b
  induction b using Finsupp.induction_linear with
  | zero => rw [slantHom_zero, show bd R (0 : (Fin (m + 1) → Γ) →₀ R) = 0 from map_zero _, slantHom_zero]; exact zero_comp
  | add a b ha hb =>
    rw [slantHom_add, show bd R (a + b) = bd R a + bd R b from map_add _ _ _, slantHom_add, ← ha, ← hb]
    exact Preadditive.add_comp _ _ _ _ _ _
  | single g r =>
    obtain ⟨f, hf⟩ := slantHom_neg R X (Γ := Γ) (m := m)
    have e : bd R (Finsupp.single g r) = Finsupp.single (fun i => g i.succ) r +
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r := by
      have := groupHomology.inhomogeneousChains.d_single (A := Rep.trivial R Γ R) m g r
      refine this.trans ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul R]
      simp
    have d : ((chainsN R).obj (BX Γ X)).d (m + 1) m =
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((BX Γ X).δ i) :=
      AlgebraicTopology.alternatingFaceMapComplex_obj_d _ m
    rw [e, ← hf (_ + _), map_add, map_sum, d, slantHom_single]
    have e2 : ∀ j : Fin (m + 1), f ((-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r) =
        (-1 : ℤ) ^ ((j : ℕ) + 1) • (ULift.up r : ULift.{1} R) • (free R).map (grpPt X (j.contractNth (· * ·) g)) :=
      fun j => by rw [map_zsmul, hf, slantHom_single]
    rw [Finset.sum_congr rfl fun j _ => e2 j, hf, slantHom_single]
    erw [Preadditive.comp_sum]
    rw [Fin.sum_univ_succ]
    congr 1
    · erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).1]
      exact one_smul ℤ _
    · refine Finset.sum_congr rfl fun j _ => ?_
      erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).2 j]
      rfl

theorem sch_d (R : Type) [CommRing R] (X : Scheme.{0}) : ((chains R).obj (sch.obj X)).d (-1) 0 = 0 := by
  have d : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((sch.obj X).δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0
  have d0 : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = 0 := by
    rw [d, Fin.sum_univ_two]
    have : (sch.obj X).δ (0 : Fin (0 + 2)) = (sch.obj X).δ 1 := rfl
    rw [this]; simp; rfl
  have := ((chainsN R).obj (sch.obj X)).extend_d_eq ComplexShape.embeddingDownNat (i := 0 + 1) (j := 0) (i' := -1) (j' := 0)
    (by simp) (by simp)
  refine this.trans ?_
  rw [d0]; simp; rfl

theorem single_congr {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q q' : ℤ} (f : K.X p ⟶ L.X q)
    (n m : ℤ) (hm : n + 1 = m) (hq : q + 1 = q') (hK : K.d (p - 1) p = 0) :
    δ n m (Cochain.single f n) = Cochain.single (f ≫ L.d q q') m := by
  rw [Cochain.δ_single f n m hm (p - 1) q' (by omega) hq, hK]
  simp

theorem deltaCo_of (h : HomD) : DeltaCo := by
  intro R _ Γ _ X
  refine ⟨fun c => ?_, fun m b => ?_⟩
  · unfold slantCo
    rw [single_congr _ _ _ rfl rfl (sch_d R X)]
    have z : IsZero (((chains R).obj (BX Γ X)).X (-((0 : ℕ) : ℤ) + 1)) :=
      ((chainsN R).obj (BX Γ X)).isZero_extend_X ComplexShape.embeddingDownNat _ (fun i hi => by
        simp at hi; omega)
    rw [z.eq_of_tgt (_ ≫ _) 0]
    simp
  · unfold slantCo
    rw [single_congr (q' := -(m : ℤ)) _ _ _ (by omega) (by omega) (sch_d R X)]
    congr 1
    have := ((chainsN R).obj (BX Γ X)).extend_d_eq ComplexShape.embeddingDownNat (i := m + 1) (j := m)
      (i' := -((m + 1 : ℕ) : ℤ)) (j' := -(m : ℤ)) (by simp) (by simp)
    unfold slantV
    rw [← h R Γ X m b]
    erw [this, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    rfl

theorem gmap1 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c : Fin n) (ha : a.val = c.val)
    (hb : b.val = c.val + 1) : (show Γ from (grpSimplex g).map f) = (g c)⁻¹ := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain rfl : a = c := ha
  obtain rfl : b = a + 1 := hb
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹) a hc

theorem gmap2 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c d : Fin n) (ha : a.val = c.val)
    (hd : d.val = c.val + 1) (hb : b.val = c.val + 2) : (show Γ from (grpSimplex g).map f) = (g c * g d)⁻¹ := by
  have h1 : a ≤ d.castSucc := by rw [Fin.le_def]; simp; omega
  have h2 : d.castSucc ≤ b := by rw [Fin.le_def]; simp; omega
  have e := (grpSimplex g).map_comp (homOfLE h1) (homOfLE h2)
  have e1 := gmap1 g _ _ (homOfLE h1) c ha (by simpa using hd)
  have e2 := gmap1 g _ _ (homOfLE h2) d (by simp) (by omega)
  rw [mul_inv_rev, ← e1, ← e2]
  exact e

theorem nerve_ext {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : ∀ (i : Fin m) (f : j.succAbove i.castSucc ⟶ j.succAbove i.succ), (show Γ from (grpSimplex g).map f) = (g' i)⁻¹) :
    (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g' := by
  refine ComposableArrows.ext (fun _ => rfl) fun i hi => ?_
  erw [Category.id_comp, Category.comp_id]
  exact (h ⟨i, hi⟩ _).trans (gmap1 g' _ _ _ ⟨i, hi⟩ rfl rfl).symm

theorem nerve_zero {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) :
    (nerve (SingleObj Γ)).δ 0 (grpSimplex g) = grpSimplex (fun i => g i.succ) :=
  nerve_ext g _ 0 fun i f => gmap1 g _ _ f i.succ (by simp) (by simp)

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (i : Fin n) : (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  by_cases h : i.val < j.val
  · rw [if_pos h, if_pos (show i.castSucc < j from h)]; rfl
  · rw [if_neg h, if_neg (show ¬ i.castSucc < j from h)]; rfl

theorem nerve_succ {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (j : Fin (m + 1)) :
    (nerve (SingleObj Γ)).δ j.succ (grpSimplex g) = grpSimplex (j.contractNth (· * ·) g) := by
  refine nerve_ext g _ _ fun i f => ?_
  have a := val_succAbove j.succ i.castSucc
  have b := val_succAbove j.succ i.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at a b
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_pos (by omega)]; rfl) (by rw [b, if_pos (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    exact gmap2 g _ _ f _ _ (by rw [a, if_pos (by omega)]; rfl) rfl (by rw [b, if_neg (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_neg (by omega)]; rfl) (by rw [b, if_neg (by omega)]; rfl)

theorem ev_pres (P Q : Spc) (n : SimplexCategoryᵒᵖ) : PreservesLimit (pair P Q) ((evaluation SimplexCategoryᵒᵖ PSh).obj n) :=
  (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit

theorem lift_fst {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u : W ⟶ P.obj n) (v : W ⟶ Q.obj n) :
    haveI := ev_pres P Q n
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.fst : P ⨯ Q ⟶ P).app n = u ∧
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.snd : P ⨯ Q ⟶ Q).app n = v := by
  haveI := ev_pres P Q n
  constructor
  · erw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  · erw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

theorem prod_ext {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u v : W ⟶ (P ⨯ Q).obj n)
    (h1 : u ≫ (prod.fst : P ⨯ Q ⟶ P).app n = v ≫ (prod.fst : P ⨯ Q ⟶ P).app n)
    (h2 : u ≫ (prod.snd : P ⨯ Q ⟶ Q).app n = v ≫ (prod.snd : P ⨯ Q ⟶ Q).app n) : u = v := by
  haveI := ev_pres P Q n
  exact BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q) h1 h2

theorem face_of {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g') : grpPt X g ≫ (BX Γ X).δ j = grpPt X g' := by
  have a := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk (m + 1))) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  have b := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk m)) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g', naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  refine prod_ext _ _ ?_ ?_
  · refine Eq.trans ?_ b.1.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    refine (congrArg (· ≫ (cst (SingleObj Γ)).δ j) a.1).trans ?_
    ext U x
    exact h
  · refine Eq.trans ?_ b.2.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    exact congrArg (· ≫ (sch.obj X).δ j) a.2

theorem faces : Faces := fun _ _ X _ g =>
  ⟨face_of X g _ _ (nerve_zero g), fun j => face_of X g _ _ (nerve_succ g j)⟩

theorem goal : LateralTheory.E.EtaleChapterDThree := goal_of (deltaCo_of (homD_of faces))

end LateralTheory.E.t_D3Cut
