import Development.EtaleCohomology.EtaleSheaves.LeafSSCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafTermsPf

variable {R : Type} [CommRing R]

theorem HKpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem HKpull_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem finite_of_retract {K L : Cx R} (s : K ⟶ L) (t : L ⟶ K) (h : s ≫ t = 𝟙 K) (F : Shv R) (n : ℤ)
    (hL : Finite (HK R L F n)) : Finite (HK R K F n) :=
  Finite.of_surjective (HK.pull R s F n) (fun x =>
    ⟨HK.pull R t F n x, by rw [← HKpull_comp, h, HKpull_id]⟩)

theorem finite_of_iso {A B : Shv R} (e : A ≅ B) (F : Shv R) (n : ℤ)
    (hB : Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj B) F n)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj A) F n) :=
  finite_of_retract _ _ (((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).mapIso e).hom_inv_id) F n hB

theorem d_const_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat
    (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
  change (((chainsN R).obj (disc.obj P)).extend ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [h]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    simp [chainsN, Fin.sum_univ_two, SimplicialObject.δ, disc]
    first
      | (erw [neg_one_smul, one_smul, add_neg_cancel])
      | (simp only [one_smul, neg_smul]; exact add_neg_cancel _)
      | abel
    all_goals rfl
  rw [this]; simp

def proj0 (P : PSh) : (chains R).obj (disc.obj P) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (disc.obj P)).X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i = -1 := by simp at hi; omega
    subst this; rw [d_const_zero]; simp)

theorem etale_chain_complex_degree_zero_incl_proj_eq_id (P : PSh) : LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (disc.obj P)) ≫ proj0 P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, proj0]

theorem finite_single_of_H (Z : Scheme.{0}) (F : Shv R) (m : ℤ) (h : Finite (H R (sch.obj Z) F m)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj Z))) F m) :=
  finite_of_iso (chainsXIso R (disc.obj (yoneda.obj Z)) 0).symm F m
    (finite_of_retract _ _ (etale_chain_complex_degree_zero_incl_proj_eq_id (R := R) (yoneda.obj Z)) F m h)

section Geo
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

abbrev W (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin n => Y) (fun _ => f)

def toPb (n : ℕ) : W f (n + 1) ⟶ pullback (WidePullback.base (fun _ : Fin n => f)) f :=
  pullback.lift (WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.succ) (by simp))
    (WidePullback.π _ 0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

def ofPb (n : ℕ) : pullback (WidePullback.base (fun _ : Fin n => f)) f ⟶ W f (n + 1) :=
  WidePullback.lift (pullback.snd _ _ ≫ f)
    (Fin.cases (pullback.snd _ _) (fun j => pullback.fst _ _ ≫ WidePullback.π _ j))
    (by intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [pullback.condition, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

theorem toPb_ofPb (n : ℕ) : toPb f n ≫ ofPb f n = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, Category.id_comp]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_zero]; rw [toPb, pullback.lift_snd]
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_succ]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π]
  · simp only [Category.assoc, Category.id_comp]
    rw [ofPb, WidePullback.lift_base, toPb, pullback.lift_snd_assoc, WidePullback.π_arrow]

theorem ofPb_toPb (n : ℕ) : ofPb f n ≫ toPb f n = 𝟙 _ := by
  apply pullback.hom_ext
  · apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π, ofPb, WidePullback.lift_π]
      simp only [Fin.cases_succ]
    · simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base, ofPb, WidePullback.lift_base, pullback.condition]
  · simp only [Category.assoc, Category.id_comp]
    rw [toPb, pullback.lift_snd, ofPb, WidePullback.lift_π]
    simp only [Fin.cases_zero]

theorem base_zero_iso : IsIso (WidePullback.base (fun _ : Fin 0 => f)) :=
  ⟨⟨WidePullback.lift (𝟙 X) (fun j => j.elim0) (fun j => j.elim0), by
    refine ⟨WidePullback.hom_ext _ _ _ (fun j => j.elim0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]), by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]⟩⟩⟩

theorem base_proper [IsProper f] : ∀ n : ℕ, IsProper (WidePullback.base (fun _ : Fin n => f))
  | 0 => by
    have := base_zero_iso f
    first | infer_instance | exact MorphismProperty.of_isIso (P := @IsProper) _
  | n + 1 => by
    have := base_proper n
    have hi : IsIso (toPb f n) := ⟨⟨ofPb f n, toPb_ofPb f n, ofPb_toPb f n⟩⟩
    have : WidePullback.base (fun _ : Fin (n + 1) => f) = toPb f n ≫ pullback.fst _ _ ≫ WidePullback.base _ := by
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base]
    rw [this]
    infer_instance

def eIso (n : ℕ) : yoneda.obj (W f n) ≅ widePullback (yoneda.obj X) (fun _ : Fin n => yoneda.obj Y) (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda _ ≪≫ HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

end Geo

theorem LeafTerms_of : LateralTheory.E.LeafSSCut.LeafTerms := by
  intro _ R _ F Y X f _ r m hZ
  refine finite_of_iso ((chainsXIso R (cech f) r) ≪≫ (free R).mapIso (eIso f (r + 1)).symm) F m ?_
  exact finite_single_of_H _ F m (hZ _ _ (base_proper f (r + 1)))

end LateralTheory.E.LeafTermsPf
