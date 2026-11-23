import Development.EtaleCohomology.EtaleSheaves.ConeExcision

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcPf

namespace LateralTheory.E.LeafSqPf

def LeafSqFree : Prop := ∀ (R : Type) [CommRing R] {P U E' E : PSh} (fst : P ⟶ U) (snd : P ⟶ E') (f : U ⟶ E) [Mono f]
  (g : E' ⟶ E), IsPullback fst snd f g →
  (∀ (T : Scheme.{0}) (y : E.obj (op T)), EtLoc T fun V k =>
    (∃ u : U.obj (op V), f.app (op V) u = E.map k.op y) ∨ ∃ a : E'.obj (op V), g.app (op V) a = E.map k.op y) →
  (∀ (T : Scheme.{0}) (a b : E'.obj (op T)), g.app (op T) a = g.app (op T) b → EtLoc T fun V k =>
    E'.map k.op a = E'.map k.op b ∨ ∃ u : U.obj (op V), f.app (op V) u = E.map k.op (g.app (op T) a)) →
  IsPushout ((free R).map snd) ((free R).map fst) ((free R).map g) ((free R).map f)

theorem sq_comm (R : Type) [CommRing R] {U E' E : Spc} (f : U ⟶ E) (g : E' ⟶ E) (n : ℤ) :
    ((chains R).map (pullback.snd f g)).f n ≫ ((chains R).map g).f n =
      ((chains R).map (pullback.fst f g)).f n ≫ ((chains R).map f).f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp,
    pullback.condition]

theorem LeafSq_of (hFree : LeafSqFree) : LeafSq := by
  intro R _ U E' E f _ g h1 h2 n
  by_cases h : ∃ p : ℕ, ComplexShape.embeddingDownNat.f p = n
  · obtain ⟨p, hp⟩ := h
    have hpb : IsPullback ((pullback.fst f g).app (op (SimplexCategory.mk p)))
        ((pullback.snd f g).app (op (SimplexCategory.mk p)))
        (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))) :=
      (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have : Mono (f.app (op (SimplexCategory.mk p))) := (NatTrans.mono_iff_mono_app f).1 ‹_› _
    have key := hFree R _ _ _ _ hpb (fun T y => h1 p T y) (fun T a b hab => h2 p T a b hab)
    show IsPushout (HomologicalComplex.extendMap ((chainsN R).map (pullback.snd f g)) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map (pullback.fst f g)) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f n)
    rw [HomologicalComplex.extendMap_f _ _ hp, HomologicalComplex.extendMap_f _ _ hp,
      HomologicalComplex.extendMap_f _ _ hp, HomologicalComplex.extendMap_f _ _ hp]
    refine key.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (pullback f g)) _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj E') _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj U) _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj E) _ hp).symm ?_ ?_ ?_ ?_ <;>
      exact (Iso.inv_hom_id_assoc _ _).symm
  · simp only [not_exists] at h
    have hz : ∀ X : Spc, IsZero (((chains R).obj X).X n) := fun X =>
      HomologicalComplex.isZero_extend_X ((chainsN R).obj X) ComplexShape.embeddingDownNat n h
    have := (hz _).isIso (hz _) (((chains R).map (pullback.snd f g)).f n)
    have := (hz _).isIso (hz _) (((chains R).map f).f n)
    exact IsPushout.of_horiz_isIso ⟨sq_comm R f g n⟩

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

def LocOnto {R : Type} [CommRing R] {MB MC MD : PMod R} (c : MB ⟶ MD) (d : MC ⟶ MD) : Prop :=
  ∀ (T : Scheme.{0}) (z : MD.obj (op T)), EtLoc T fun V k =>
    ∃ (x : MB.obj (op V)) (y : MC.obj (op V)), (c.app (op V)).hom x + (d.app (op V)).hom y = (MD.map k.op).hom z

def LocKer {R : Type} [CommRing R] {MA MB MC MD : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC) (c : MB ⟶ MD) (d : MC ⟶ MD) :
    Prop :=
  ∀ (T : Scheme.{0}) (x : MB.obj (op T)) (y : MC.obj (op T)), (c.app (op T)).hom x + (d.app (op T)).hom y = 0 →
    EtLoc T fun V k => ∃ w : MA.obj (op V), (a.app (op V)).hom w = (MB.map k.op).hom x ∧
      (b.app (op V)).hom w = -(MC.map k.op).hom y

def LeafSheafPush : Prop := ∀ (R : Type) [CommRing R] {MA MB MC MD : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC)
  (c : MB ⟶ MD) (d : MC ⟶ MD), a ≫ c = b ≫ d → LocOnto c d → LocKer a b c d →
  IsPushout ((presheafToSheaf Scheme.etaleTopology.{0} _).map a) ((presheafToSheaf Scheme.etaleTopology.{0} _).map b) ((presheafToSheaf Scheme.etaleTopology.{0} _).map c)
    ((presheafToSheaf Scheme.etaleTopology.{0} _).map d)

def LeafFreeLoc : Prop := ∀ (R : Type) [CommRing R] {P U E' E : PSh} (fst : P ⟶ U) (snd : P ⟶ E') (f : U ⟶ E) [Mono f]
  (g : E' ⟶ E), IsPullback fst snd f g →
  (∀ (T : Scheme.{0}) (y : E.obj (op T)), EtLoc T fun V k =>
    (∃ u : U.obj (op V), f.app (op V) u = E.map k.op y) ∨ ∃ a : E'.obj (op V), g.app (op V) a = E.map k.op y) →
  (∀ (T : Scheme.{0}) (a b : E'.obj (op T)), g.app (op T) a = g.app (op T) b → EtLoc T fun V k =>
    E'.map k.op a = E'.map k.op b ∨ ∃ u : U.obj (op V), f.app (op V) u = E.map k.op (g.app (op T) a)) →
  LocOnto ((freeP R).map g) ((freeP R).map f) ∧
    LocKer ((freeP R).map snd) ((freeP R).map fst) ((freeP R).map g) ((freeP R).map f)

theorem LeafSqFree_of (hSP : LeafSheafPush) (hFL : LeafFreeLoc) : LeafSqFree := by
  intro R _ P U E' E fst snd f _ g hpb h1 h2
  obtain ⟨hon, hker⟩ := hFL R fst snd f g hpb h1 h2
  have hw : (freeP R).map snd ≫ (freeP R).map g = (freeP R).map fst ≫ (freeP R).map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]
  exact hSP R _ _ _ _ hw hon hker

theorem square_of_pushout_and_free_local (hSP : LeafSheafPush) (hFL : LeafFreeLoc) : LeafSq := LeafSq_of (LeafSqFree_of hSP hFL)

end LateralTheory.E.LeafSqPf
