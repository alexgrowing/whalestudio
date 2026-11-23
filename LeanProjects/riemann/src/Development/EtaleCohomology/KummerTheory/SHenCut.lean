import Development.EtaleCohomology.KummerTheory.InjSlice
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Functor.Flat

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SHenCut

def Sat {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (e : Cocone D) : Prop :=
  ∀ (j : J) (B : CommRingCat.{0}) (φ : D.obj j ⟶ B) (β : B ⟶ e.pt), φ.hom.Etale → φ ≫ β = e.ι.app j →
    ∃ (k : J) (f : j ⟶ k) (γ : B ⟶ D.obj k), φ ≫ γ = D.map f ∧ γ ≫ e.ι.app k = β

def UnitLift {C Ω : Type} [CommRing C] [CommRing Ω] (ε : C →+* Ω) : Prop := ∀ x, ε x ≠ 0 → IsUnit x

def RootLift {C Ω : Type} [CommRing C] [CommRing Ω] (ε : C →+* Ω) : Prop :=
  ∀ f : Polynomial C, f.Monic → ∀ ω : Ω, f.eval₂ ε ω = 0 → f.derivative.eval₂ ε ω ≠ 0 → ∃ a : C, f.IsRoot a ∧ ε a = ω

def SatUnit : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
  (e : Cocone D), IsField e.pt → Sat D e → UnitLift (hc.desc e).hom

def SatRoot : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
  (e : Cocone D), IsField e.pt → Sat D e → RootLift (hc.desc e).hom

def SHOfLift : Prop := ∀ (C Ω : Type) [CommRing C] [Field Ω] [IsAlgClosed Ω] (ε : C →+* Ω), UnitLift ε → RootLift ε → SH C

abbrev Et : MorphismProperty CommRingCat.{0} := RingHom.toMorphismProperty RingHom.Etale

instance : Et.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
instance : Et.RespectsIso := RingHom.toMorphismProperty_respectsIso_iff.1 RingHom.Etale.respectsIso
instance : Et.IsStableUnderComposition where
  comp_mem f g hf hg := RingHom.Etale.stableUnderComposition f.hom g.hom hf hg
instance : Et.ContainsIdentities where
  id_mem _ := RingHom.Etale.of_bijective Function.bijective_id
instance : Et.HasOfPrecompProperty Et where
  of_precomp {A B C} f g hf hfg := by
    have hf' : f.hom.Etale := hf
    have hfg' : (g.hom.comp f.hom).Etale := hfg
    algebraize [f.hom, g.hom, g.hom.comp f.hom]
    exact Algebra.Etale.of_restrictScalars A B C

abbrev Nb {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) := CostructuredArrow (MorphismProperty.Under.forget Et ⊤ R) (Under.mk s)

instance {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : EssentiallySmall.{0} (Nb s) := by
  have : EssentiallySmall.{0} (MorphismProperty.Under Et ⊤ R) := essentiallySmall_of_le (fun _ _ f hf => by
    have hf' : f.hom.Etale := hf
    exact RingHom.FiniteType.of_finitePresentation (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf').2.2) R
  infer_instance

instance {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : IsFiltered (Nb s) := by
  have : RepresentablyCoflat (MorphismProperty.Under.forget Et ⊤ R) := coflat_of_preservesFiniteColimits _
  infer_instance

def Nb.ring {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : Nb s ⥤ CommRingCat.{0} :=
  CostructuredArrow.proj _ _ ⋙ MorphismProperty.Under.forget Et ⊤ R ⋙ Under.forget R

theorem exists_sat {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ CommRingCat.{0}) (u : (Functor.const J).obj R ⟶ D) (e : D ⟶ (Functor.const J).obj Ω),
    Sat D (Cocone.mk Ω e) ∧ ∀ j, (u.app j).hom.Etale ∧ u.app j ≫ e.app j = s := by
  let E := equivSmallModel.{0} (Nb s)
  refine ⟨SmallModel.{0} (Nb s), inferInstance, IsFiltered.of_equivalence E, E.inverse ⋙ Nb.ring s,
    { app := fun j => (E.inverse.obj j).left.hom, naturality := fun j k f => ?_ },
    { app := fun j => (E.inverse.obj j).hom.right, naturality := fun j k f => ?_ }, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact (Category.id_comp _).trans (Under.w ((MorphismProperty.Under.forget Et ⊤ R).map (E.inverse.map f).left)).symm
  · exact (congrArg (fun t => t.right) (CostructuredArrow.w (E.inverse.map f))).trans (Category.comp_id _).symm
  · intro j B φ β hφ hβ
    have hw : (E.inverse.obj j).left.hom ≫ (E.inverse.obj j).hom.right = s := Under.w (E.inverse.obj j).hom
    let A : MorphismProperty.Under Et ⊤ R := MorphismProperty.Under.mk ⊤ ((E.inverse.obj j).left.hom ≫ φ)
      (Et.comp_mem _ _ (E.inverse.obj j).left.prop hφ)
    let N : Nb s := CostructuredArrow.mk (Y := A) (Under.homMk β
      ((Category.assoc _ _ _).trans ((congrArg (fun t => (E.inverse.obj j).left.hom ≫ t) hβ).trans hw)))
    let m : E.inverse.obj j ⟶ N := CostructuredArrow.homMk (MorphismProperty.Under.homMk φ rfl trivial)
      (Under.UnderMorphism.ext hβ)
    refine ⟨E.functor.obj N, E.inverse.preimage (m ≫ E.unit.app N), (Nb.ring s).map (E.unit.app N), ?_, ?_⟩
    · change (Nb.ring s).map m ≫ _ = (Nb.ring s).map (E.inverse.map _)
      rw [Functor.map_preimage, Functor.map_comp]
    · exact congrArg (fun t => t.right) (CostructuredArrow.w (E.unit.app N))
  · exact (E.inverse.obj j).left.prop
  · exact Under.w (E.inverse.obj j).hom

theorem goal_of (h1 : SatUnit) (h2 : SatRoot) (h3 : SHOfLift) : LateralTheory.KummerTheory.StrictHenselization := by
  intro R 𝔭
  let Ω := AlgebraicClosure 𝔭.asIdeal.ResidueField
  let s : R →+* Ω := (algebraMap 𝔭.asIdeal.ResidueField Ω).comp (algebraMap R 𝔭.asIdeal.ResidueField)
  have hs : RingHom.ker s = 𝔭.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap 𝔭.asIdeal.ResidueField Ω).injective,
      Ideal.ker_algebraMap_residueField]
  obtain ⟨J, _, _, D, u, e, hsat, hu⟩ := exists_sat (Ω := CommRingCat.of Ω) (CommRingCat.ofHom s)
  have hF : IsField (Cocone.mk (F := D) (CommRingCat.of Ω) e).pt := Field.toIsField Ω
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, u,
    h3 _ Ω _ (h1 D _ (colimit.isColimit D) _ hF hsat) (h2 D _ (colimit.isColimit D) _ hF hsat), fun j => ⟨(hu j).1, ?_⟩⟩
  let ej : D.obj j →+* Ω := (e.app j).hom
  refine ⟨⟨RingHom.ker ej, RingHom.ker_isPrime ej⟩, ?_⟩
  have : ej.comp (u.app j).hom = s := congrArg CommRingCat.Hom.hom (hu j).2
  exact (congrArg RingHom.ker this).trans hs

end LateralTheory.KummerTheory.SHenCut

end
