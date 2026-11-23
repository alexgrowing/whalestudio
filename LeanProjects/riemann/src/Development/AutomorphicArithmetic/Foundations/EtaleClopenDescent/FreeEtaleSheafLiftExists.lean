import Mathlib
import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.LeafShMapZeroOf

open CategoryTheory Limits

namespace UpperTheory.Cb.HomologyEvaluation

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem comp_reassoc_six {D : Type*} [Category D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : D} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (f₆ : A₅ ⟶ A₆) :
    ((f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ f₅) ≫ f₆ = (f₁ ≫ f₂) ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
  simp

private theorem single_homologyMap (L : CochainComplex C ℤ) (X : C) (c : X ⟶ L.cycles 0) :
    ∃ φ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ L,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        HomologicalComplex.homologyMap φ 0 = c ≫ L.homologyπ 0 := by
  refine ⟨HomologicalComplex.mkHomFromSingle (c ≫ L.iCycles 0) (fun k _ => by simp), ?_⟩
  have h1 : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).homologyπ 0 := by
    rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom]
    simp
  rw [h1, Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0)]
  simp

private theorem exists_cycles (K : DerivedCategory C) :
    ∃ (Z : C) (π : Z ⟶ (DerivedCategory.homologyFunctor C 0).obj K), Epi π ∧
      ∀ (X : C) (c : X ⟶ Z), ∃ x : (DerivedCategory.singleFunctor C 0).obj X ⟶ K,
        (DerivedCategory.homologyFunctor C 0).map x =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X ≫ c ≫ π := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨(DerivedCategory.Q (C := C)).objObjPreimageIso K⟩⟩
  refine ⟨L.cycles 0, L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
    (DerivedCategory.homologyFunctor C 0).map e.hom, ?_, fun X c => ?_⟩
  · have i0 : Epi (L.homologyπ 0) := inferInstance
    have i1 : IsIso ((DerivedCategory.homologyFunctorFactors C 0).inv.app L) :=
      inferInstanceAs (IsIso ((DerivedCategory.homologyFunctorFactors C 0).app L).inv)
    have i2 : Epi ((DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
        (DerivedCategory.homologyFunctor C 0).map e.hom) := epi_comp _ _
    exact @epi_comp _ _ _ _ _ _ i0 _ i2
  obtain ⟨φ, hφ⟩ := single_homologyMap L X c
  refine ⟨(DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
      (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := by
    have h3 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
        (DerivedCategory.homologyFunctor C 0).map (((DerivedCategory.singleFunctorsPostcompQIso C).hom.hom 0).app X) ≫
        𝟙 _ ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := rfl
    have hm : (DerivedCategory.homologyFunctor C 0).map (NatTrans.app (𝟙 ((DerivedCategory.singleFunctors C).functor 0)) X) =
        (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) := rfl
    rw [h3, DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
    erw [Category.id_comp]
    exact congrArg (fun t => t ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) hm
  rw [h2, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  have hφ' : HomologicalComplex.homologyMap φ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom ≫ c ≫ L.homologyπ 0 := by
    rw [← hφ, Iso.hom_inv_id_assoc]
  have n' : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫ HomologicalComplex.homologyMap φ 0) ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app L :=
    (Iso.eq_comp_inv ((DerivedCategory.homologyFunctorFactors C 0).app L)).2
      (DerivedCategory.homologyFunctorFactors_hom_naturality φ 0)
  have key : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctor C 0).map e.hom =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) ≫ c ≫
        L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
          (DerivedCategory.homologyFunctor C 0).map e.hom := by
    rw [n', hφ']
    exact comp_reassoc_six _ _ _ _ _ _
  exact key

end UpperTheory.Cb.HomologyEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.HomologyEvaluation
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

variable {B : Scheme.{0}} {q : ℕ}

private def ev (H : SShv B q) (U : B.Etale) :
    ((F0 B q).obj U ⟶ H) ≃ ToType (H.obj.obj (op U)) :=
  ((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H).trans
    ((((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv
      (uliftYoneda.{1}.obj U) H.obj).trans uliftYonedaEquiv)

private theorem ev_comp {H H' : SShv B q} (g : H ⟶ H') (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    ev H' U (t ≫ g) = g.hom.app (op U) (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_right t g
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_right
    (X := uliftYoneda.{1}.obj U) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t) ((sheafToPresheaf _ _).map g)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U) H'.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_comp _ _)

private theorem ev_map (H : SShv B q) {U U' : B.Etale} (a : U' ⟶ U) (t : (F0 B q).obj U ⟶ H) :
    ev H U' ((F0 B q).map a ≫ t) = H.obj.map a.op (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_left
      (X' := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U'))
      (X := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U))
      (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).map
        (uliftYoneda.{1}.map a)) t
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_left
    (uliftYoneda.{1}.map a) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U') H.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_naturality _ a.op).symm

private theorem lift_local {Z H : SShv B q} (π : Z ⟶ H) [Epi π] (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    Cov U (fun U' a => ∃ c : (F0 B q).obj U' ⟶ Z, c ≫ π = (F0 B q).map a ≫ t) := by
  haveI : EssentiallySmall.{1} B.Etale := inferInstance
  haveI : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) := inferInstance
  have hls : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} (ZMod q))) π).2 inferInstance
  refine ⟨Presheaf.imageSieve π.hom (ev H U t),
    Presheaf.imageSieve_mem (EtTop B) π.hom (U := op U) (ev H U t), fun U' a ha => ?_⟩
  obtain ⟨z, hz⟩ := ha
  refine ⟨(ev Z U').symm z, (ev H U').injective ?_⟩
  rw [ev_comp, ev_map, Equiv.apply_symm_apply]
  exact hz

end UpperTheory.Cb.HomologyEvaluation

open UpperTheory.Cb.HomologyEvaluation LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShMapZeroPf.Gen in
theorem UpperTheory.Cb.free_etale_sheaf_lift_exists :
    LateralTheory.E.LeafShMapZeroPf.EtaleLift' := by
  intro B q K U s
  obtain ⟨Z, π, hπ, hlift⟩ := exists_cycles (C := SShv B q) K
  refine (lift_local π U ((e0 B q).inv.app U ≫ s)).mono fun U' a hc => ?_
  obtain ⟨c, hc⟩ := hc
  obtain ⟨x, hx⟩ := hlift _ c
  refine ⟨x, ?_⟩
  have he : (e0 B q).hom.app U' =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0).hom.app ((F0 B q).obj U') :=
    Category.comp_id _
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  have s1 : s = (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by
    rw [Iso.hom_inv_id_app_assoc]
  have h1 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
        (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by rw [← s1]
  have h2 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
      (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s := by
    rw [reassoc_of% n]
    rfl
  have h3 : (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ c ≫ π := by rw [hc]
  have h4 : (e0 B q).hom.app U' ≫ c ≫ π =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x := by
    rw [he]; exact hx.symm
  exact h1.trans (h2.trans (h3.trans h4))
