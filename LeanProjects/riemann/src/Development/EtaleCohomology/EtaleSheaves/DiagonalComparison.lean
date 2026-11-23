import Development.EtaleCohomology.EtaleSheaves.LeafSSCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiagonalComparison

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp, Cochain.ofHom_comp]

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro a b g
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  apply NatTrans.ext; funext n
  erw [NatTrans.comp_app]
  simp only [cechAug, Arrow.augmentedCechNerve_hom_app]
  erw [WidePullback.lift_base]
  rfl

theorem lift_iso {C : Type*} [Category C] {B A : C} (h : A ⟶ B)
    [HasWidePullback B (fun _ : Fin 1 => A) (fun _ => h)] :
    IsIso (WidePullback.lift h (fun _ : Fin 1 => 𝟙 A) (fun _ => Category.id_comp _) :
      A ⟶ widePullback B (fun _ : Fin 1 => A) (fun _ => h)) := by
  refine ⟨⟨WidePullback.π _ 0, ?_, ?_⟩⟩
  · rw [WidePullback.lift_π]
  apply WidePullback.hom_ext
  · intro j
    obtain rfl := Fin.fin_one_eq_zero j
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

instance isIso_cech_nerve_diagonal_app_degree_zero {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((diag f).app (op (SimplexCategory.mk 0))) :=
  lift_iso (C := PSh) (yoneda.map f)

instance isIso_etale_chains_map_cech_diagonal_degree_zero {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    IsIso (((chains R).map (diag f)).f 0) := by
  change IsIso ((HomologicalComplex.extendMap ((chainsN R).map (diag f)) ComplexShape.embeddingDownNat).f 0)
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]
  have : IsIso (((chainsN R).map (diag f)).f 0) := by
    change IsIso ((free R).map ((diag f).app (op (SimplexCategory.mk 0))))
    infer_instance
  infer_instance

theorem etale_chains_degree_zero_inclusion_factors_through_cech_diagonal {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (inv (((chains R).map (diag f)).f 0)) ≫
      LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (sch.obj Y)) ≫ (chains R).map (diag f) =
    LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f)) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self]

theorem LeafCompare_of : LateralTheory.E.LeafSSCut.LeafCompare := by
  intro _ R _ F Y X f n hE _
  have key : ∀ x, pull R (sch.map f) F n x = 0 →
      HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n (pull R (cechAug f) F n x) = 0 := by
    intro x hx
    rw [← etale_chains_degree_zero_inclusion_factors_through_cech_diagonal f, hkpull_comp, hkpull_comp]
    have h0 : HK.pull R ((chains R).map (diag f)) F n (pull R (cechAug f) F n x) = 0 := by
      rw [← hx, ← diag_aug f, pull_comp]; rfl
    rw [h0, map_zero, map_zero]
  let φ : (pull R (sch.map f) F n).ker →
      (HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n).ker :=
    fun x => ⟨pull R (cechAug f) F n x.1, AddMonoidHom.mem_ker.2 (key x.1 (AddMonoidHom.mem_ker.1 x.2))⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (hE n).1 (congrArg Subtype.val hxy)
  exact Finite.of_injective φ hφ

end LateralTheory.E.DiagonalComparison
