import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppSub

variable {R : Type} [CommRing R] (Z : Scheme.{0} → Prop) (hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  change (F.obj.map (f ≫ g).op).hom a = _
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

def sv {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sieve U where
  arrows V g := Z V ∨ Sec.res g a = 0
  downward_closed {V W} g hg f := by
    rcases hg with h | h
    · exact Or.inl (hZ _ _ f h)
    · right
      rw [res_comp, h]; exact map_zero (F.obj.map f.op).hom

theorem loc_iff {F : Shv R} {U : Scheme.{0}} (a : Sec F U) :
    (Loc U fun V g => Z V ∨ Sec.res g a = 0) ↔ sv Z hZ a ∈ Scheme.etaleTopology U := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact GrothendieckTopology.superset_covering _ (fun V g hg => h V g hg) hS
  · intro h
    exact ⟨_, h, fun V g hg => hg⟩

def supp (F : Shv R) (U : Scheme.{0}) : Submodule (ULift.{1} R) (Sec F U) where
  carrier := {a | sv Z hZ a ∈ Scheme.etaleTopology U}
  zero_mem' := by
    refine GrothendieckTopology.superset_covering _ (fun V g _ => Or.inr (map_zero _)) (GrothendieckTopology.top_mem _ U)
  add_mem' {a b} ha hb := by
    refine GrothendieckTopology.superset_covering _ (fun V g hg => ?_) (GrothendieckTopology.intersection_covering _ ha hb)
    rcases hg.1 with h | h
    · exact Or.inl h
    rcases hg.2 with h' | h'
    · exact Or.inl h'
    · right; change (F.obj.map g.op).hom (a + b) = 0; rw [map_add]; exact (congrArg₂ (· + ·) h h').trans (add_zero 0)
  smul_mem' c a ha := by
    refine GrothendieckTopology.superset_covering _ (fun V g hg => ?_) ha
    rcases hg with h | h
    · exact Or.inl h
    · right; change (F.obj.map g.op).hom (c • a) = 0; rw [map_smul]; exact (congrArg (c • ·) h).trans (smul_zero c)

theorem supp_res {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.res g a ∈ supp Z hZ F V := by
  refine GrothendieckTopology.superset_covering _ (fun W f hf => ?_) (Scheme.etaleTopology.pullback_stable g (show sv Z hZ a ∈ Scheme.etaleTopology U from ha))
  change Z W ∨ Sec.res (f ≫ g) a = 0 at hf
  rw [res_comp] at hf
  exact hf

def suppP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (supp Z hZ F U.unop)
  map {U V} g := ModuleCat.ofHom ((F.obj.map g).hom.restrict (fun a ha => supp_res Z hZ g.unop ha))
  map_id U := by
    ext ⟨a, ha⟩
    change (F.obj.map (𝟙 U)).hom a = a
    rw [F.obj.map_id]; rfl
  map_comp {U V W} f g := by
    ext ⟨a, ha⟩
    change (F.obj.map (f ≫ g)).hom a = (F.obj.map g).hom ((F.obj.map f).hom a)
    rw [F.obj.map_comp]; rfl

def suppT (F : Shv R) : Subfunctor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) where
  obj U := {a | a ∈ supp Z hZ F U.unop}
  map {U V} g a ha := supp_res Z hZ g.unop ha

theorem sheafT (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property)

theorem suppT_isSheaf (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (suppT Z hZ F).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (sheafT F)]
  intro U s hs
  change sv Z hZ (F := F) (U := U.unop) s ∈ Scheme.etaleTopology U.unop
  refine Scheme.etaleTopology.transitive hs _ (fun V f hf => ?_)
  have hf' : sv Z hZ (Sec.res f s) ∈ Scheme.etaleTopology V := hf
  refine Scheme.etaleTopology.superset_covering (fun W h hh => ?_) hf'
  change Z W ∨ Sec.res (h ≫ f) s = 0
  rw [res_comp]
  exact hh

theorem sectionsWithSupport_isSheaf (F : Shv R) : Presheaf.IsSheaf Scheme.etaleTopology (suppP Z hZ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso _ (NatIso.ofComponents (fun U => Iso.refl _) (fun _ => rfl)).symm (suppT_isSheaf Z hZ F)

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom a = (F.obj.map g.op ≫ φ.hom.app (op V)).hom a
  rw [φ.hom.naturality]

theorem supp_map {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.map φ a ∈ supp Z hZ G U := by
  refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) (show sv Z hZ a ∈ Scheme.etaleTopology U from ha)
  rcases hg with h | h
  · exact Or.inl h
  · right
    change Sec.res g (Sec.map φ a) = 0
    rw [res_map, h]
    exact map_zero (φ.hom.app (op V)).hom

def suppS (F : Shv R) : Shv R := ⟨suppP Z hZ F, sectionsWithSupport_isSheaf Z hZ F⟩

def suppF : Shv R ⥤ Shv R where
  obj F := suppS Z hZ F
  map {F G} φ := ObjectProperty.homMk
    { app U := ModuleCat.ofHom ((φ.hom.app U).hom.restrict (fun a ha => supp_map Z hZ φ ha))
      naturality U V g := by
        ext ⟨a, ha⟩
        exact Subtype.ext (res_map φ g.unop a).symm }
  map_id F := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

def suppι : suppF Z hZ ⟶ 𝟭 (Shv R) where
  app F := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (supp Z hZ F U.unop).subtype
      naturality U V g := by
        ext ⟨a, ha⟩
        rfl }
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

instance : (suppF Z hZ (R := R)).PreservesZeroMorphisms where
  map_zero F G := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    apply Subtype.ext
    change ((0 : F ⟶ G).hom.app U).hom a = 0
    simp

def suppCx (C : Cx R) : Cx R := ((suppF Z hZ).mapHomologicalComplex _).obj C

def suppCxι (C : Cx R) : suppCx Z hZ C ⟶ C where
  f n := (suppι Z hZ).app (C.X n)
  comm' i j _ := (suppι Z hZ).naturality (C.d i j)

theorem exists_supp_sub : ∀ (R : Type) [CommRing R] (C : Cx R) (Z : Scheme.{0} → Prop), (∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V) → ∃ (D : Cx R) (ι : D ⟶ C), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) ∧ ∀ n U (a : Sec (C.X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => Z V ∨ Sec.res g a = 0 := by
  intro R _ C Z hZ
  refine ⟨suppCx Z hZ C, suppCxι Z hZ C, fun n U => ?_, fun n U a => ?_⟩
  · intro b b' h
    exact Subtype.ext (p := fun x => x ∈ supp Z hZ (C.X n) U) h
  · rw [loc_iff Z hZ]
    constructor
    · rintro ⟨b, rfl⟩
      exact (show ↥(supp Z hZ (C.X n) U) from b).2
    · intro h
      exact ⟨(⟨a, h⟩ : ↥(supp Z hZ (C.X n) U)), rfl⟩

end GlobalTheory.EtC.SuppSub
