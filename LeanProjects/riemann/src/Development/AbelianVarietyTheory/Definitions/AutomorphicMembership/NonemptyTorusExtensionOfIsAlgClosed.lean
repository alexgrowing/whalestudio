import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnifNontrivialTorus

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

namespace GlobalTheory.TorusPart

variable {S S' S'' : Scheme.{0}}

def Cochar (G : Over S) [GrpObj G] : Type := {l : Gm S ⟶ G // IsMonHom l}

def cocharSubgroup (G : Over S) [GrpObj G] [IsCommMonObj G] : Subgroup (Gm S ⟶ G) where
  carrier := {l | IsMonHom l}
  mul_mem' := fun {a b} (_ : IsMonHom a) (_ : IsMonHom b) => Serre.isMonHom_mul a b
  one_mem' := Serre.isMonHom_one
  inv_mem' := fun {a} (_ : IsMonHom a) => by
    rw [← zpow_neg_one]; exact Serre.isMonHom_zpow a (-1)

namespace Cochar

section Basic

variable {G H K : Over S} [GrpObj G] [GrpObj H] [GrpObj K]

instance isMonHom (l : Cochar G) : IsMonHom l.1 := l.2

@[ext] theorem ext {l m : Cochar G} (h : l.1 = m.1) : l = m := Subtype.ext h

variable [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K]

instance : AddCommGroup (Cochar G) := inferInstanceAs (AddCommGroup (Additive (cocharSubgroup G)))

@[simp] theorem val_add (l m : Cochar G) : (l + m).1 = l.1 * m.1 := rfl

@[simp] theorem val_zero : (0 : Cochar G).1 = 1 := rfl

@[simp] theorem val_neg (l : Cochar G) : (-l).1 = l.1⁻¹ := rfl

@[simp] theorem val_zsmul (n : ℤ) (l : Cochar G) : (n • l).1 = l.1 ^ n := rfl

def map (u : G ⟶ H) [IsMonHom u] : Cochar G →+ Cochar H :=
  AddMonoidHom.mk' (fun l => ⟨l.1 ≫ u, inferInstance⟩) fun l m => ext (MonObj.mul_comp l.1 m.1 u)

@[simp] theorem map_val (u : G ⟶ H) [IsMonHom u] (l : Cochar G) : (map u l).1 = l.1 ≫ u := rfl

theorem map_id (l : Cochar G) : map (𝟙 G) l = l := ext (Category.comp_id _)

theorem map_comp (u : G ⟶ H) (v : H ⟶ K) [IsMonHom u] [IsMonHom v] (l : Cochar G) :
    map (u ≫ v) l = map v (map u l) := ext (Category.assoc _ _ _).symm

def actHom {O : Type} [CommRing O] (a : OAct O G) (c : O) : Cochar G →+ Cochar G :=
  haveI := a.hom c; map (a.act c)

@[simp] theorem actHom_val {O : Type} [CommRing O] (a : OAct O G) (c : O) (l : Cochar G) :
    (actHom a c l).1 = l.1 ≫ a.act c := rfl

@[reducible] def module {O : Type} [CommRing O] (a : OAct O G) : Module O (Cochar G) where
  smul c l := actHom a c l
  one_smul l := ext (show l.1 ≫ a.act 1 = l.1 by rw [a.one, Category.comp_id])
  mul_smul c d l := ext (show l.1 ≫ a.act (c * d) = (l.1 ≫ a.act d) ≫ a.act c by
    rw [mul_comm, a.mul, Category.assoc])
  smul_zero c := map_zero (actHom a c)
  smul_add c := map_add (actHom a c)
  add_smul c d l := ext (show l.1 ≫ a.act (c + d) = (l.1 ≫ a.act c) * (l.1 ≫ a.act d) by
    rw [a.add, MonObj.comp_mul])
  zero_smul l := ext (show l.1 ≫ a.act 0 = 1 by rw [Serre.act_zero, MonObj.comp_one])

end Basic

end Cochar

section Pull

variable {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {G'' : Over S''} [GrpObj G'']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

def pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) : splitTorus S' X ⟶ G' :=
  Over.homMk (h.1.lift (bcMap f X ≫ i.left) (splitTorus S' X).hom (by
    rw [Category.assoc, Over.w, SplitTorus.bcMap_hom])) (h.1.lift_snd _ _ _)

theorem pullTorus_left (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ φ = bcMap f X ≫ i.left := h.1.lift_fst _ _ _

theorem hom_ext_of_pullback (h : IsGrpPullback G' G f φ) {T : Over S'} {x y : T ⟶ G'}
    (e : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext e ((Over.w x).trans (Over.w y).symm))

theorem eq_pullTorus_iff (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (i' : splitTorus S' X ⟶ G') : i' = pullTorus h i ↔ i'.left ≫ φ = bcMap f X ≫ i.left :=
  ⟨fun e => e ▸ pullTorus_left h i, fun e => hom_ext_of_pullback h (e.trans (pullTorus_left h i).symm)⟩

instance isMonHom_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) [IsMonHom i] :
    IsMonHom (pullTorus h i) :=
  Out.PullGtPf.isMonHom_of_grpPullback (SplitTorus.isGrpPullback_bcMap f X) h i _ (pullTorus_left h i)

theorem pullTorus_mul (h : IsGrpPullback G' G f φ) (i j : splitTorus S X ⟶ G) :
    pullTorus h (i * j) = pullTorus h i * pullTorus h j := by
  let b : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S X :=
    Over.homMk (bcMap f X) (SplitTorus.bcMap_hom f X)
  have k := h.2 _ (pullTorus h i) (pullTorus h j) (b ≫ i) (b ≫ j) (pullTorus_left h i).symm
    (pullTorus_left h j).symm
  rw [← MonObj.comp_mul] at k
  exact ((eq_pullTorus_iff h _ _).2 k.symm).symm

theorem bcMap_id : bcMap (𝟙 S) X = 𝟙 _ := by
  apply pullback.hom_ext
  · exact (SplitTorus.bcMap_torusFst _ _).trans (Category.id_comp _).symm
  · exact (SplitTorus.bcMap_hom _ _).trans ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem bcMap_comp (g : S'' ⟶ S') (f : S' ⟶ S) : bcMap (g ≫ f) X = bcMap g X ≫ bcMap f X := by
  apply pullback.hom_ext
  · have e : (bcMap g X ≫ bcMap f X) ≫ Rosenlicht.torusFst S X = Rosenlicht.torusFst S'' X := by
      rw [Category.assoc, SplitTorus.bcMap_torusFst, SplitTorus.bcMap_torusFst]
    exact (SplitTorus.bcMap_torusFst _ _).trans e.symm
  · have e : (bcMap g X ≫ bcMap f X) ≫ (splitTorus S X).hom = (splitTorus S'' X).hom ≫ g ≫ f := by
      rw [Category.assoc, SplitTorus.bcMap_hom, SplitTorus.bcMap_hom_assoc]
    exact (SplitTorus.bcMap_hom _ _).trans e.symm

theorem pullTorus_pullTorus {g : S'' ⟶ S'} {φ' : G''.left ⟶ G'.left} {f'' : S'' ⟶ S}
    {φ'' : G''.left ⟶ G.left} (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ)
    (h'' : IsGrpPullback G'' G f'' φ'') (ef : f'' = g ≫ f) (eφ : φ'' = φ' ≫ φ)
    (i : splitTorus S X ⟶ G) : pullTorus h' (pullTorus h i) = pullTorus h'' i := by
  subst ef eφ
  rw [eq_pullTorus_iff, ← Category.assoc, pullTorus_left, Category.assoc, pullTorus_left, bcMap_comp,
    Category.assoc]

theorem pullTorus_torusMap_comp {Y : Type} [AddCommGroup Y] (h : IsGrpPullback G' G f φ)
    (i : splitTorus S X ⟶ G) (u : X →+ Y) :
    pullTorus h (torusMap S u ≫ i) = torusMap S' u ≫ pullTorus h i := by
  rw [eq_comm, eq_pullTorus_iff, Over.comp_left, Over.comp_left, Category.assoc, pullTorus_left,
    ← Category.assoc, SplitTorus.torusMap_bcMap, Category.assoc]

theorem pullTorus_comp {H : Over S} [GrpObj H] {H' : Over S'} [GrpObj H'] {ψ : H'.left ⟶ H.left}
    (h : IsGrpPullback G' G f φ) (k : IsGrpPullback H' H f ψ) (u : G ⟶ H) (u' : G' ⟶ H')
    (e : u'.left ≫ ψ = φ ≫ u.left) (i : splitTorus S X ⟶ G) :
    pullTorus k (i ≫ u) = pullTorus h i ≫ u' := by
  rw [eq_comm, eq_pullTorus_iff, Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc,
    pullTorus_left, Category.assoc]

theorem exists_isKernel_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    {B : Over S} [GrpObj B] (q : G ⟶ B) [IsMonHom q] (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ q' : G' ⟶ (Over.pullback f).obj B, IsMonHom q' ∧
      IsPullback (pullTorus h i) (toUnit _) q' η[(Over.pullback f).obj B] := by
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  refine ⟨e.hom ≫ (Over.pullback f).map q, inferInstance, ?_⟩
  refine IsPullback.of_iso (hk.map (Over.pullback f)) (bcIso f X).symm e.symm
    (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq]
    refine hom_ext_of_pullback (isGrpPullback_pullback G f) ?_
    rw [ExtUnique.pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
      heφ, pullTorus_left, SplitTorus.bcIso_inv_bcMap_assoc]
  · exact toUnit_unique _ _
  · simp
  · simp

variable [IsCommMonObj G] [IsCommMonObj G'] [IsCommMonObj G'']

namespace Cochar

def pull (h : IsGrpPullback G' G f φ) : Cochar G →+ Cochar G' :=
  AddMonoidHom.mk' (fun l => ⟨pullTorus h l.1, inferInstance⟩) fun l m => ext (pullTorus_mul h l.1 m.1)

theorem pull_val (h : IsGrpPullback G' G f φ) (l : Cochar G) : (pull h l).1 = pullTorus h l.1 := rfl

theorem pull_left (h : IsGrpPullback G' G f φ) (l : Cochar G) :
    (pull h l).1.left ≫ φ = bcMap f (ULift ℤ) ≫ l.1.left := pullTorus_left h l.1

theorem eq_pull_iff (h : IsGrpPullback G' G f φ) (l : Cochar G) (l' : Cochar G') :
    l' = pull h l ↔ l'.1.left ≫ φ = bcMap f (ULift ℤ) ≫ l.1.left :=
  Subtype.ext_iff.trans (eq_pullTorus_iff h l.1 l'.1)

theorem pull_id (h : IsGrpPullback G G (𝟙 S) (𝟙 G.left)) (l : Cochar G) : pull h l = l :=
  ((eq_pull_iff h l l).2 (by rw [bcMap_id, Category.id_comp, Category.comp_id])).symm

theorem pull_pull {g : S'' ⟶ S'} {φ' : G''.left ⟶ G'.left} {f'' : S'' ⟶ S}
    {φ'' : G''.left ⟶ G.left} (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ)
    (h'' : IsGrpPullback G'' G f'' φ'') (ef : f'' = g ≫ f) (eφ : φ'' = φ' ≫ φ) (l : Cochar G) :
    pull h' (pull h l) = pull h'' l := ext (pullTorus_pullTorus h' h h'' ef eφ l.1)

theorem pull_comp {g : S'' ⟶ S'} {φ' : G''.left ⟶ G'.left} (h' : IsGrpPullback G'' G' g φ')
    (h : IsGrpPullback G' G f φ) (l : Cochar G) : pull (h'.comp h) l = pull h' (pull h l) :=
  (pull_pull h' h _ rfl rfl l).symm

theorem pull_map {H : Over S} [GrpObj H] [IsCommMonObj H] {H' : Over S'} [GrpObj H'] [IsCommMonObj H']
    {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G f φ) (k : IsGrpPullback H' H f ψ) (u : G ⟶ H)
    (u' : G' ⟶ H') [IsMonHom u] [IsMonHom u'] (e : u'.left ≫ ψ = φ ≫ u.left) (l : Cochar G) :
    pull k (map u l) = map u' (pull h l) := ext (pullTorus_comp h k u u' e l.1)

theorem pull_actHom {O : Type} [CommRing O] (h : IsGrpPullback G' G f φ) (a : OAct O G) (a' : OAct O G')
    (e : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) (c : O) (l : Cochar G) :
    pull h (actHom a c l) = actHom a' c (pull h l) := ext (pullTorus_comp h h _ _ (e c) l.1)

theorem pull_of_iso {H : Over S} [GrpObj H] [IsCommMonObj H] (e : H ≅ G) [IsMonHom e.hom] (l : Cochar G) :
    pull (isGrpPullback_of_iso e) l = map e.inv l :=
  ((eq_pull_iff _ _ _).2 (by
    rw [bcMap_id, Category.id_comp, ← Over.comp_left, map_val, Category.assoc, e.inv_hom_id,
      Category.comp_id])).symm

theorem pull_injective [QuasiCompact f] [IsSchemeTheoreticallyDominant f] [IsSeparated G.hom]
    (h : IsGrpPullback G' G f φ) : Function.Injective (pull h) := fun l m e => by
  have : Flat (splitTorusAff ZU (ULift.{0} ℤ)).hom :=
    (ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  have : Flat (Gm S).hom := inferInstanceAs (Flat (pullback.snd _ _))
  refine ext (ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap f _) ?_)
  rw [← pull_left h, ← pull_left h, e]

end Cochar

end Pull

abbrev Char (G : Over S) [GrpObj G] [IsCommMonObj G] : Type := Cochar G →+ ℤ

namespace Char

section

variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {G'' : Over S''} [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def comap (u : G ⟶ H) [IsMonHom u] : Char H →+ Char G := AddMonoidHom.compHom' (Cochar.map u)

@[simp] theorem comap_apply (u : G ⟶ H) [IsMonHom u] (χ : Char H) (l : Cochar G) :
    comap u χ l = χ (Cochar.map u l) := rfl

def pull (h : IsGrpPullback G' G f φ) : Char G' →+ Char G := AddMonoidHom.compHom' (Cochar.pull h)

@[simp] theorem pull_apply (h : IsGrpPullback G' G f φ) (χ : Char G') (l : Cochar G) :
    pull h χ l = χ (Cochar.pull h l) := rfl

theorem pull_id (h : IsGrpPullback G G (𝟙 S) (𝟙 G.left)) (χ : Char G) : pull h χ = χ :=
  AddMonoidHom.ext fun l => congrArg χ (Cochar.pull_id h l)

theorem pull_pull {g : S'' ⟶ S'} {φ' : G''.left ⟶ G'.left} {f'' : S'' ⟶ S}
    {φ'' : G''.left ⟶ G.left} (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ)
    (h'' : IsGrpPullback G'' G f'' φ'') (ef : f'' = g ≫ f) (eφ : φ'' = φ' ≫ φ) (χ : Char G'') :
    pull h (pull h' χ) = pull h'' χ :=
  AddMonoidHom.ext fun l => congrArg χ (Cochar.pull_pull h' h h'' ef eφ l)

theorem pull_comp {g : S'' ⟶ S'} {φ' : G''.left ⟶ G'.left} (h' : IsGrpPullback G'' G' g φ')
    (h : IsGrpPullback G' G f φ) (χ : Char G'') : pull (h'.comp h) χ = pull h (pull h' χ) :=
  (pull_pull h' h _ rfl rfl χ).symm

theorem pull_bijective {h : IsGrpPullback G' G f φ} (hb : Function.Bijective (Cochar.pull h)) :
    Function.Bijective (pull h) := by
  let e := AddEquiv.ofBijective _ hb
  refine ⟨fun χ χ' k => AddMonoidHom.ext fun l => ?_, fun χ => ⟨χ.comp e.symm.toAddMonoidHom,
    AddMonoidHom.ext fun l => congrArg χ (e.symm_apply_apply l)⟩⟩
  obtain ⟨l, rfl⟩ := hb.2 l
  exact DFunLike.congr_fun k l

@[reducible] def module {O : Type} [CommRing O] (a : OAct O G) (σ : O →+* O) : Module O (Char G) :=
  letI := Cochar.module a
  { smul c χ := χ.comp (Cochar.actHom a (σ c))
    one_smul χ := AddMonoidHom.ext fun l => congrArg χ (show σ 1 • l = l by rw [map_one, one_smul])
    mul_smul c d χ := AddMonoidHom.ext fun l => congrArg χ
      (show σ (c * d) • l = σ d • σ c • l by rw [mul_comm, map_mul, mul_smul])
    smul_zero c := rfl
    smul_add c χ χ' := rfl
    add_smul c d χ := AddMonoidHom.ext fun l =>
      (show χ (σ (c + d) • l) = χ (σ c • l) + χ (σ d • l) by rw [map_add, add_smul, map_add])
    zero_smul χ := AddMonoidHom.ext fun l =>
      (show χ (σ 0 • l) = 0 by rw [map_zero, zero_smul, map_zero]) }

end

end Char

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def CocharOf (t : SAB H S) : Type := Cochar t.G

def CharOf (t : SAB H S) : Type := Char t.G

namespace CocharOf

variable {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

instance (t : SAB H S) : AddCommGroup (CocharOf t) := inferInstanceAs (AddCommGroup (Cochar t.G))

instance (t : SAB H S) : Module (𝓞 E) (CocharOf t) := Cochar.module t.act

@[simp] theorem smul_val (a : 𝓞 E) (l : CocharOf t) : (a • l).1 = l.1 ≫ t.act.act a := rfl

def pull (m : SABMap t' t f) : CocharOf t →ₗ[𝓞 E] CocharOf t' where
  toFun l := Cochar.pull m.cart l
  map_add' := map_add (Cochar.pull m.cart)
  map_smul' a l := Cochar.pull_actHom m.cart t.act t'.act m.act a l

theorem pull_apply (m : SABMap t' t f) (l : CocharOf t) : pull m l = Cochar.pull m.cart l := rfl

end CocharOf

namespace CharOf

variable {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

instance (t : SAB H S) : AddCommGroup (CharOf t) := inferInstanceAs (AddCommGroup (Char t.G))

instance (t : SAB H S) : FunLike (CharOf t) (CocharOf t) ℤ :=
  inferInstanceAs (FunLike (Cochar t.G →+ ℤ) (Cochar t.G) ℤ)

instance (t : SAB H S) : AddMonoidHomClass (CharOf t) (CocharOf t) ℤ :=
  inferInstanceAs (AddMonoidHomClass (Cochar t.G →+ ℤ) (Cochar t.G) ℤ)

instance (t : SAB H S) : Module (𝓞 E) (CharOf t) := Char.module t.act (H.bar : 𝓞 E →+* 𝓞 E)

@[ext] theorem ext {χ χ' : CharOf t} (h : ∀ l, χ l = χ' l) : χ = χ' := DFunLike.ext _ _ h

@[simp] theorem add_apply (χ χ' : CharOf t) (l : CocharOf t) : (χ + χ') l = χ l + χ' l := rfl

@[simp] theorem zero_apply (l : CocharOf t) : (0 : CharOf t) l = 0 := rfl

@[simp] theorem smul_apply (a : 𝓞 E) (χ : CharOf t) (l : CocharOf t) :
    (a • χ) l = χ (H.bar a • l) := rfl

theorem comap_act (a : 𝓞 E) (χ : CharOf t) :
    (haveI := t.act.hom a; Char.comap (t.act.act a) χ : CharOf t) = H.bar a • χ := by
  letI := H.starRing
  refine ext fun l => ?_
  rw [smul_apply, show H.bar (H.bar a) = a from star_star a]
  rfl

def pull (m : SABMap t' t f) : CharOf t' →ₗ[𝓞 E] CharOf t where
  toFun χ := Char.pull m.cart χ
  map_add' := map_add (Char.pull m.cart)
  map_smul' a χ := ext fun l => congrArg χ ((CocharOf.pull m).map_smul (H.bar a) l).symm

@[simp] theorem pull_apply (m : SABMap t' t f) (χ : CharOf t') (l : CocharOf t) :
    pull m χ l = χ (CocharOf.pull m l) := rfl

theorem pull_pull {t'' : SAB H S''} {g : S'' ⟶ S'} {f'' : S'' ⟶ S} (m' : SABMap t'' t' g)
    (m : SABMap t' t f) (m'' : SABMap t'' t f'') (ef : f'' = g ≫ f) (eφ : m''.φ = m'.φ ≫ m.φ)
    (χ : CharOf t'') : pull m (pull m' χ) = pull m'' χ :=
  Char.pull_pull m'.cart m.cart m''.cart ef eφ χ

end CharOf

end Triple

section Torus

variable {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def torusCochar (S : Scheme.{0}) (l : X →+ ℤ) : Gm S ⟶ splitTorus S X :=
  torusMap S ((AddEquiv.ulift.symm : ℤ ≃+ ULift.{0} ℤ).toAddMonoidHom.comp l)

instance (l : X →+ ℤ) : IsMonHom (torusCochar S l) := SplitTorus.isMonHom_torusMap _

theorem torusCochar_appTop_chi (l : X →+ ℤ) (x : X) :
    (torusCochar S l).left.appTop.hom (Rosenlicht.chi X x) = Rosenlicht.chi (ULift.{0} ℤ) (ULift.up (l x)) :=
  SplitTorus.torusMap_appTop_chi _ x

theorem torusCochar_comp (l : Y →+ ℤ) (u : X →+ Y) :
    torusCochar S (l.comp u) = torusCochar S l ≫ torusMap S u :=
  by rw [torusCochar, torusCochar, ← SplitTorus.torusMap_comp, AddMonoidHom.comp_assoc]

theorem torusCochar_add (l m : X →+ ℤ) :
    torusCochar S (l + m) = torusCochar S l * torusCochar S m := by
  rw [torusCochar, torusCochar, torusCochar, AddMonoidHom.comp_add, SplitTorus.torusMap_add]

def ofTorus (i : splitTorus S X ⟶ G) [IsMonHom i] : (X →+ ℤ) →+ Cochar G :=
  AddMonoidHom.mk' (fun l => ⟨torusCochar S l ≫ i, inferInstance⟩) fun l m => Cochar.ext
    ((congrArg (· ≫ i) (torusCochar_add l m)).trans (MonObj.mul_comp _ _ i))

@[simp] theorem ofTorus_val (i : splitTorus S X ⟶ G) [IsMonHom i] (l : X →+ ℤ) :
    (ofTorus i l).1 = torusCochar S l ≫ i := rfl

theorem pull_ofTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) [IsMonHom i] (l : X →+ ℤ) :
    Cochar.pull h (ofTorus i l) = ofTorus (pullTorus h i) l :=
  Cochar.ext (pullTorus_torusMap_comp h i _)

theorem pull_ofTorus_of_left (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) [IsMonHom i]
    (i' : splitTorus S' X ⟶ G') [IsMonHom i'] (e : i'.left ≫ φ = bcMap f X ≫ i.left) (l : X →+ ℤ) :
    Cochar.pull h (ofTorus i l) = ofTorus i' l := by
  obtain rfl := (eq_pullTorus_iff h i i').2 e
  exact pull_ofTorus h i l

theorem map_ofTorus {H : Over S} [GrpObj H] [IsCommMonObj H] (u : G ⟶ H) [IsMonHom u]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (l : X →+ ℤ) :
    Cochar.map u (ofTorus i l) = ofTorus (i ≫ u) l := Cochar.ext (Category.assoc _ _ _)

theorem ofTorus_torusMap_comp (i : splitTorus S X ⟶ G) [IsMonHom i] (u : X →+ Y) (l : Y →+ ℤ) :
    ofTorus (torusMap S u ≫ i) l = ofTorus i (l.comp u) :=
  Cochar.ext (by rw [ofTorus_val, ofTorus_val, torusCochar_comp, Category.assoc])

theorem ofTorus_injective [Nonempty S] (i : splitTorus S X ⟶ G) [IsMonHom i] [Mono i] :
    Function.Injective (ofTorus i) := fun l m e => by
  have k := SplitTorus.torusMap_injective ((cancel_mono i).1 (congrArg Subtype.val e))
  exact AddMonoidHom.ext fun x => congrArg ULift.down (DFunLike.congr_fun k x)

theorem mem_range_ofTorus [ConnectedSpace S] (i : splitTorus S X ⟶ G) [IsMonHom i] (l : Cochar G)
    (u : Gm S ⟶ splitTorus S X) [IsMonHom u] (e : u ≫ i = l.1) : ∃ m, ofTorus i m = l := by
  obtain ⟨v, rfl⟩ := SplitTorus.exists_eq_torusMap u
  exact ⟨(AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom.comp v, Cochar.ext e⟩

theorem ofTorus_id_bijective [ConnectedSpace S] :
    Function.Bijective (ofTorus (𝟙 (splitTorus S X))) :=
  ⟨ofTorus_injective _, fun l => mem_range_ofTorus _ l l.1 (Category.comp_id _)⟩

theorem ofTorus_bijective_of_isKernel [ConnectedSpace S] (i : splitTorus S X ⟶ G) [IsMonHom i]
    {B : Over S} [GrpObj B] (q : G ⟶ B) [IsMonHom q] (hk : IsPullback i (toUnit _) q η[B])
    (hB : ∀ u : Gm S ⟶ B, IsMonHom u → u = toUnit _ ≫ η[B]) : Function.Bijective (ofTorus i) := by
  have : Mono i := ⟨fun a b e => hk.hom_ext e (toUnit_unique _ _)⟩
  refine ⟨ofTorus_injective i, fun l => ?_⟩
  let u := hk.lift l.1 (toUnit _) (hB _ inferInstance)
  have hu : u ≫ i = l.1 := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono i, MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc, Category.assoc, hu,
      MonObj.mul_comp]
  exact mem_range_ofTorus i l u hu

theorem subsingleton_cochar_of_isProper {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (B : Over (Sp A)) [GrpObj B] [IsProper B.hom] : Subsingleton (Cochar B) :=
  ⟨fun l m => Cochar.ext ((splitTorus_hom_proper_trivial_local A _ B l.1 l.2).trans
    (splitTorus_hom_proper_trivial_local A _ B m.1 m.2).symm)⟩

theorem ofTorus_bijective_of_isProper {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {G : Over (Sp A)} [GrpObj G] [IsCommMonObj G] (i : splitTorus (Sp A) X ⟶ G) [IsMonHom i]
    {B : Over (Sp A)} [GrpObj B] [IsProper B.hom] (q : G ⟶ B) [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) : Function.Bijective (ofTorus i) :=
  haveI : ConnectedSpace (Sp A) := SplitTorus.connectedSpace_of_isLocalRing A
  ofTorus_bijective_of_isKernel i q hk fun u hu => splitTorus_hom_proper_trivial_local A _ B u hu

theorem ofTorus_pullTorus_bijective {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {G₀ : Over (Sp A)} [GrpObj G₀] [IsCommMonObj G₀] {p : Sp A ⟶ S} {ψ : G₀.left ⟶ G.left}
    (h : IsGrpPullback G₀ G p ψ) (i : splitTorus S X ⟶ G) [IsMonHom i]
    {B : Over S} [GrpObj B] [IsProper B.hom] (q : G ⟶ B) [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) : Function.Bijective (ofTorus (pullTorus h i)) := by
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus h i q hk
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact ofTorus_bijective_of_isProper _ q' hk'

theorem pull_bijective_of_ofTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) [IsMonHom i]
    (hi : Function.Bijective (ofTorus i)) (hi' : Function.Bijective (ofTorus (pullTorus h i))) :
    Function.Bijective (Cochar.pull h) := by
  refine (Function.Bijective.of_comp_iff _ hi).1 ?_
  rwa [show Cochar.pull h ∘ ofTorus i = ofTorus (pullTorus h i) from funext (pull_ofTorus h i)]

section Ext

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] [IsCommMonObj G]

theorem ofTorus_bijective_of_torusExtension (T : TorusExtension G) :
    letI := T.addCommGroup; haveI := T.i_hom; Function.Bijective (ofTorus T.i) := by
  letI := T.addCommGroup; letI := T.grpB
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  exact ofTorus_bijective_of_isProper T.i T.q T.isKernel

theorem Cochar.pull_bijective_of_torusExtension (hT : Nonempty (TorusExtension G))
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {G₀ : Over (Sp A)} [GrpObj G₀] [IsCommMonObj G₀] {p : Sp A ⟶ Sp K} {ψ : G₀.left ⟶ G.left}
    (h : IsGrpPullback G₀ G p ψ) : Function.Bijective (Cochar.pull h) := by
  obtain ⟨T⟩ := hT
  letI := T.addCommGroup; letI := T.grpB
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  exact pull_bijective_of_ofTorus h T.i (ofTorus_bijective_of_torusExtension T)
    (ofTorus_pullTorus_bijective h T.i T.q T.isKernel)

theorem Char.pull_bijective_of_torusExtension (hT : Nonempty (TorusExtension G))
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {G₀ : Over (Sp A)} [GrpObj G₀] [IsCommMonObj G₀] {p : Sp A ⟶ Sp K} {ψ : G₀.left ⟶ G.left}
    (h : IsGrpPullback G₀ G p ψ) : Function.Bijective (Char.pull h) :=
  Char.pull_bijective (Cochar.pull_bijective_of_torusExtension hT h)

end Ext

theorem nonempty_torusExtension_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G : Over (Sp Ω)}
    [GrpObj G] (h : IsSemiAbelian G) : Nonempty (TorusExtension G) := by
  obtain ⟨T⟩ := h.fibres Ω (𝟙 _)
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G (𝟙 _)) (isGrpPullback_of_iso (Iso.refl G))
  exact ⟨torusExtOfIso e T⟩

theorem CharOf.pull_bijective_of_isAlgClosed {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Ω A : Type} [Field Ω] [IsAlgClosed Ω] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {t : SAB H (Sp Ω)} {t' : SAB H (Sp A)} {p : Sp A ⟶ Sp Ω} (m : SABMap t' t p) :
    Function.Bijective (CharOf.pull m) :=
  Char.pull_bijective_of_torusExtension (nonempty_torusExtension_of_isAlgClosed t.semi) m.cart

theorem eval_bijective (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Function.Bijective (AddMonoidHom.eval : X →+ (X →+ ℤ) →+ ℤ) := by
  have hb := Module.bijective_dual_eval ℤ X
  refine ⟨fun x y e => hb.1 (LinearMap.ext fun l => DFunLike.congr_fun e l.toAddMonoidHom), fun F => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (F.comp (LinearMap.toAddMonoidHom' (R₁ := ℤ) (R₂ := ℤ))).toIntLinearMap
  exact ⟨x, AddMonoidHom.ext fun l => LinearMap.congr_fun hx l.toIntLinearMap⟩

variable [Module.Free ℤ X] [Module.Finite ℤ X]

def charEquivOfTorus (i : splitTorus S X ⟶ G) [IsMonHom i] (hi : Function.Bijective (ofTorus i)) :
    X ≃+ Char G :=
  (AddEquiv.ofBijective _ (eval_bijective X)).trans
    (AddEquiv.addMonoidHomCongrLeft (AddEquiv.ofBijective _ hi))

@[simp] theorem charEquivOfTorus_apply (i : splitTorus S X ⟶ G) [IsMonHom i]
    (hi : Function.Bijective (ofTorus i)) (x : X) (l : X →+ ℤ) :
    charEquivOfTorus i hi x (ofTorus i l) = l x :=
  congrArg (fun m : X →+ ℤ => m x) ((AddEquiv.ofBijective _ hi).symm_apply_apply l)

theorem eq_charEquivOfTorus_iff (i : splitTorus S X ⟶ G) [IsMonHom i]
    (hi : Function.Bijective (ofTorus i)) (x : X) (χ : Char G) :
    χ = charEquivOfTorus i hi x ↔ ∀ l, χ (ofTorus i l) = l x := by
  refine ⟨fun e l => e ▸ charEquivOfTorus_apply i hi x l, fun e => AddMonoidHom.ext fun l => ?_⟩
  obtain ⟨l, rfl⟩ := hi.2 l
  rw [e, charEquivOfTorus_apply]

theorem pull_charEquivOfTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) [IsMonHom i]
    (hi : Function.Bijective (ofTorus i)) (hi' : Function.Bijective (ofTorus (pullTorus h i))) (x : X) :
    Char.pull h (charEquivOfTorus _ hi' x) = charEquivOfTorus i hi x :=
  (eq_charEquivOfTorus_iff i hi x _).2 fun l => by
    rw [Char.pull_apply, pull_ofTorus, charEquivOfTorus_apply]

def charEquivSplitTorus (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] : X ≃+ Char (splitTorus S X) :=
  charEquivOfTorus (𝟙 _) ofTorus_id_bijective

def charEquivOfTorusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] [IsCommMonObj G]
    (T : TorusExtension G) : letI := T.addCommGroup; T.X ≃+ Char G :=
  letI := T.addCommGroup; haveI := T.free; haveI := T.finite; haveI := T.i_hom
  charEquivOfTorus T.i (ofTorus_bijective_of_torusExtension T)

end Torus

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type} [CommRing A] {ρ : R →+* A}

section Coord

variable {D : Out.DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Sp A)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}

theorem ofTorus_bijective_of_gtCoord [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
    (g : Out.GtCoord I D e G) : haveI := g.i_hom; Function.Bijective (ofTorus g.i) := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact ofTorus_bijective_of_isProper g.i g.q g.isKernel

omit [IsDomain R] in

def thickPt (e : ℕ) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) : Sp A ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  spMap (Ideal.Quotient.lift _ ρ hρ)

omit [IsDomain R] in

theorem thickPt_thick (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) :
    thickPt e hρ ≫ Out.thick R I e = spMap ρ := by
  rw [thickPt, ← Spec.map_comp]; rfl

omit [IsDomain R] [IsCommMonObj G] in

def thickLift (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    G₀.left ⟶ (Out.thickObj R I e G).left :=
  pullback.lift φ (G₀.hom ≫ thickPt e hρ) (by rw [Category.assoc, thickPt_thick, h.1.w])

omit [IsDomain R] [IsCommMonObj G] in

theorem thickLift_fst (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    thickLift hρ h ≫ pullback.fst G.hom (Out.thick R I e) = φ := pullback.lift_fst _ _ _

omit [IsDomain R] [IsCommMonObj G] in

theorem isGrpPullback_thickLift (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    IsGrpPullback G₀ (Out.thickObj R I e G) (thickPt e hρ) (thickLift hρ h) :=
  (isGrpPullback_pullback G (Out.thick R I e)).cancel
    (h.congr (thickPt_thick hρ).symm (thickLift_fst hρ h).symm) (pullback.lift_snd _ _ _)

def gtTorus (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) : splitTorus (Sp A) D.X ⟶ G₀ :=
  pullTorus (isGrpPullback_thickLift hρ h) g.i

instance (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) : IsMonHom (gtTorus g hρ h) :=
  haveI := g.i_hom; isMonHom_pullTorus _ _

theorem gtTorus_left (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    (gtTorus g hρ h).left ≫ φ =
      bcMap (thickPt e hρ) D.X ≫ g.i.left ≫ pullback.fst G.hom (Out.thick R I e) := by
  have k := pullTorus_left (isGrpPullback_thickLift hρ h) g.i
  exact (congrArg (_ ≫ ·) (thickLift_fst hρ h).symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) k).trans (Category.assoc _ _ _)))

theorem pullTorus_gtTorus {A' : Type} [CommRing A'] {σ : A →+* A'} {ρ' : R →+* A'} {G₁ : Over (Sp A')}
    [GrpObj G₁] {ψ : G₁.left ⟶ G₀.left} {φ' : G₁.left ⟶ G.left} (g : Out.GtCoord I D e G)
    (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) (hρ' : ∀ x ∈ I ^ (e + 1), ρ' x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) (h' : IsGrpPullback G₁ G (spMap ρ') φ')
    (k : IsGrpPullback G₁ G₀ (spMap σ) ψ) (eρ : ρ' = σ.comp ρ) (eφ : φ' = ψ ≫ φ) :
    pullTorus k (gtTorus g hρ h) = gtTorus g hρ' h' := by
  subst eρ eφ
  have e₁ : thickPt e hρ' = spMap σ ≫ thickPt e hρ := by
    rw [thickPt, thickPt, ← Spec.map_comp]
    congr 2
    exact Ideal.Quotient.ringHom_ext rfl
  refine pullTorus_pullTorus k _ _ e₁ (pullback.hom_ext ?_ ?_) g.i
  · exact (thickLift_fst _ _).trans ((congrArg (ψ ≫ ·) (thickLift_fst hρ h).symm).trans
      (Category.assoc _ _ _).symm)
  · refine (isGrpPullback_thickLift hρ' h').1.w.trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine Eq.trans ?_ (congrArg (ψ ≫ ·) (isGrpPullback_thickLift hρ h).1.w.symm)
    rw [e₁, ← Category.assoc, ← k.1.w, Category.assoc]

theorem ofTorus_gtTorus_bijective [IsLocalRing A] [IsNoetherianRing A] [IsCommMonObj G₀]
    (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0) (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    Function.Bijective (ofTorus (gtTorus g hρ h)) := by
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact ofTorus_pullTorus_bijective _ g.i g.q g.isKernel

end Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp R)}
  {t₀ : SAB H (Sp A)}

omit [IsDomain R] in

theorem map_pow_one_eq_zero (hρ : ∀ x ∈ I, ρ x = 0) : ∀ x ∈ I ^ (0 + 1), ρ x = 0 :=
  fun x hx => hρ x (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)

namespace PELUnif

def torus (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ)) :
    splitTorus (Sp A) P.D.toPre.X ⟶ t₀.G :=
  gtTorus (P.U.gt 0) (map_pow_one_eq_zero hρ) m.cart

instance (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ)) :
    IsMonHom (torus P hρ m) := inferInstanceAs (IsMonHom (gtTorus _ _ _))

theorem torus_comp_act (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ))
    (a : 𝓞 E) : torus P hρ m ≫ t₀.act.act a =
      torusMap (Sp A) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) ≫ torus P hρ m := by
  letI := H.starRing
  obtain ⟨τ, hτ, hi⟩ := P.lin.i_lin 0 a
  have e : τ = torusMap _ (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) :=
    (SplitTorus.eq_torusMap_iff _ _).2 fun x =>
      (SplitTorus.res_pullU_charUnit τ x _).symm.trans
        ((congrArg Units.val (hτ x)).trans (SplitTorus.charUnit_val _))
  have k := isGrpPullback_thickLift (map_pow_one_eq_zero hρ) m.cart
  have c : (t₀.act.act a).left ≫ thickLift (map_pow_one_eq_zero hρ) m.cart =
      thickLift (map_pow_one_eq_zero hρ) m.cart ≫
        ((Over.pullback (Out.thick R I 0)).map (t.act.act a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (thickLift_fst _ _)).trans ((m.act a).trans ?_))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (ExtUnique.pullback_map_left_fst _ _).symm)
      exact (congrArg (· ≫ _) (thickLift_fst _ _).symm).trans (Category.assoc _ _ _)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k.1.w).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w ((Over.pullback (Out.thick R I 0)).map (t.act.act a))).symm)
      refine Eq.trans ?_ k.1.w.symm
      rw [← Category.assoc, Over.w]
  exact (pullTorus_comp k k _ _ c (P.U.gt 0).i).symm.trans
    ((congrArg (pullTorus k) (hi.trans (congrArg (· ≫ _) e))).trans (pullTorus_torusMap_comp k _ _))

def cochar (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ)) :
    (P.D.toPre.X →+ ℤ) →+ CocharOf t₀ := ofTorus (torus P hρ m)

theorem smul_cochar (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ))
    (a : 𝓞 E) (l : P.D.toPre.X →+ ℤ) : a • cochar P hρ m l =
      cochar P hρ m (l.comp (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a))) :=
  Cochar.ext (show (torusCochar _ l ≫ torus P hρ m) ≫ t₀.act.act a = torusCochar _ _ ≫ torus P hρ m by
    rw [Category.assoc, torus_comp_act, torusCochar_comp, Category.assoc])

variable [IsLocalRing A] [IsNoetherianRing A]

theorem cochar_bijective (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ)) :
    Function.Bijective (cochar P hρ m) := ofTorus_gtTorus_bijective _ _ _

def charEquivOfKer (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0) (m : SABMap t₀ t (spMap ρ)) :
    P.D.toPre.X ≃ₗ[𝓞 E] CharOf t₀ :=
  { (charEquivOfTorus (torus P hρ m) (cochar_bijective P hρ m) : P.D.toPre.X ≃+ CharOf t₀) with
    map_smul' := fun a x => ((eq_charEquivOfTorus_iff _ (cochar_bijective P hρ m) _ _).2 fun l => by
      letI := H.starRing
      refine (congrArg (charEquivOfTorus _ (cochar_bijective P hρ m) x)
        (smul_cochar P hρ m (H.bar a) l)).trans ((charEquivOfTorus_apply _ _ _ _).trans ?_)
      exact congrArg (fun c : 𝓞 E => l (c • x)) (star_star a)).symm }

@[simp] theorem charEquivOfKer_apply (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0)
    (m : SABMap t₀ t (spMap ρ)) (x : P.D.toPre.X) (l : P.D.toPre.X →+ ℤ) :
    charEquivOfKer P hρ m x (cochar P hρ m l) = l x :=
  charEquivOfTorus_apply _ (cochar_bijective P hρ m) x l

theorem pull_charEquivOfKer {A' : Type} [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A']
    {σ : A →+* A'} {ρ' : R →+* A'} {t₁ : SAB H (Sp A')} (P : PELUnif I t) (hρ : ∀ x ∈ I, ρ x = 0)
    (hρ' : ∀ x ∈ I, ρ' x = 0) (m : SABMap t₀ t (spMap ρ)) (m' : SABMap t₁ t (spMap ρ'))
    (n : SABMap t₁ t₀ (spMap σ)) (eρ : ρ' = σ.comp ρ) (eφ : m'.φ = n.φ ≫ m.φ) (x : P.D.toPre.X) :
    CharOf.pull n (charEquivOfKer P hρ' m' x) = charEquivOfKer P hρ m x :=
  (eq_charEquivOfTorus_iff _ (cochar_bijective P hρ m) _ _).2 fun l => by
    have e : CocharOf.pull n (cochar P hρ m l) = cochar P hρ' m' l :=
      Cochar.ext ((pullTorus_torusMap_comp n.cart _ _).trans
        (congrArg (_ ≫ ·) (pullTorus_gtTorus _ _ _ m.cart m'.cart n.cart eρ eφ)))
    exact (congrArg (charEquivOfKer P hρ' m' x) e).trans (charEquivOfKer_apply P hρ' m' x l)

end PELUnif

omit [IsDomain R] in

theorem map_eq_zero_of_isLocalHom [IsLocalRing R] {k : Type} [Field k] (ρ : R →+* k) [IsLocalHom ρ] :
    ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0 := fun x hx => by
  by_contra h
  exact hx (IsLocalHom.map_nonunit x (Ne.isUnit h))

def PELUnif.charEquiv [IsLocalRing R] {k : Type} [Field k] {ρ : R →+* k} [IsLocalHom ρ]
    {t₀ : SAB H (Sp k)} (P : PELUnif (IsLocalRing.maximalIdeal R) t) (m : SABMap t₀ t (spMap ρ)) :
    P.D.toPre.X ≃ₗ[𝓞 E] CharOf t₀ :=
  PELUnif.charEquivOfKer P (map_eq_zero_of_isLocalHom ρ) m

@[simp] theorem PELUnif.charEquiv_apply [IsLocalRing R] {k : Type} [Field k] {ρ : R →+* k} [IsLocalHom ρ]
    {t₀ : SAB H (Sp k)} (P : PELUnif (IsLocalRing.maximalIdeal R) t) (m : SABMap t₀ t (spMap ρ))
    (x : P.D.toPre.X) (l : P.D.toPre.X →+ ℤ) :
    PELUnif.charEquiv P m x (PELUnif.cochar P (map_eq_zero_of_isLocalHom ρ) m l) = l x :=
  PELUnif.charEquivOfKer_apply P _ m x l

end Unif

section Spec

variable {V S₁ S₀ : Scheme.{0}} {G : Over V} [GrpObj G] [IsCommMonObj G]
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {G₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  {f₁ : S₁ ⟶ V} {f₀ : S₀ ⟶ V} {φ₁ : G₁.left ⟶ G.left} {φ₀ : G₀.left ⟶ G.left}

def IsSpec (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₀ : IsGrpPullback G₀ G f₀ φ₀) (l₁ : Cochar G₁)
    (l₀ : Cochar G₀) : Prop :=
  ∃ l : Cochar G, Cochar.pull h₁ l = l₁ ∧ Cochar.pull h₀ l = l₀

theorem isSpec_pull (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₀ : IsGrpPullback G₀ G f₀ φ₀) (l : Cochar G) :
    IsSpec h₁ h₀ (Cochar.pull h₁ l) (Cochar.pull h₀ l) := ⟨l, rfl, rfl⟩

theorem IsSpec.add {h₁ : IsGrpPullback G₁ G f₁ φ₁} {h₀ : IsGrpPullback G₀ G f₀ φ₀} {l₁ m₁ : Cochar G₁}
    {l₀ m₀ : Cochar G₀} (a : IsSpec h₁ h₀ l₁ l₀) (b : IsSpec h₁ h₀ m₁ m₀) :
    IsSpec h₁ h₀ (l₁ + m₁) (l₀ + m₀) := by
  obtain ⟨l, rfl, rfl⟩ := a
  obtain ⟨m, rfl, rfl⟩ := b
  exact ⟨l + m, map_add _ _ _, map_add _ _ _⟩

theorem IsSpec.unique {h₁ : IsGrpPullback G₁ G f₁ φ₁} {h₀ : IsGrpPullback G₀ G f₀ φ₀}
    (hi : Function.Injective (Cochar.pull h₁)) {l₁ : Cochar G₁} {l₀ m₀ : Cochar G₀}
    (a : IsSpec h₁ h₀ l₁ l₀) (b : IsSpec h₁ h₀ l₁ m₀) : l₀ = m₀ := by
  obtain ⟨l, rfl, rfl⟩ := a
  obtain ⟨m, e, rfl⟩ := b
  rw [hi e]

def sp (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₀ : IsGrpPullback G₀ G f₀ φ₀)
    (hb : Function.Bijective (Cochar.pull h₁)) : Cochar G₁ →+ Cochar G₀ :=
  (Cochar.pull h₀).comp (AddEquiv.ofBijective _ hb).symm.toAddMonoidHom

def res (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₀ : IsGrpPullback G₀ G f₀ φ₀)
    (hb : Function.Bijective (Cochar.pull h₁)) : Char G₀ →+ Char G₁ :=
  AddMonoidHom.compHom' (sp h₁ h₀ hb)

variable (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₀ : IsGrpPullback G₀ G f₀ φ₀)
  (hb : Function.Bijective (Cochar.pull h₁))

@[simp] theorem sp_pull (l : Cochar G) : sp h₁ h₀ hb (Cochar.pull h₁ l) = Cochar.pull h₀ l :=
  congrArg (Cochar.pull h₀) ((AddEquiv.ofBijective _ hb).symm_apply_apply l)

theorem isSpec_iff (l₁ : Cochar G₁) (l₀ : Cochar G₀) : IsSpec h₁ h₀ l₁ l₀ ↔ sp h₁ h₀ hb l₁ = l₀ := by
  obtain ⟨l, rfl⟩ := hb.2 l₁
  rw [sp_pull]
  exact ⟨fun a => (isSpec_pull h₁ h₀ l).unique hb.1 a, fun e => e ▸ isSpec_pull h₁ h₀ l⟩

@[simp] theorem res_apply (χ : Char G₀) (l : Cochar G₁) : res h₁ h₀ hb χ l = χ (sp h₁ h₀ hb l) := rfl

theorem pull_res (χ : Char G₀) : Char.pull h₁ (res h₁ h₀ hb χ) = Char.pull h₀ χ :=
  AddMonoidHom.ext fun l => congrArg χ (sp_pull h₁ h₀ hb l)

theorem eq_res_iff (χ : Char G₀) (χ₁ : Char G₁) :
    χ₁ = res h₁ h₀ hb χ ↔ Char.pull h₁ χ₁ = Char.pull h₀ χ :=
  ⟨fun e => e ▸ pull_res h₁ h₀ hb χ,
    fun e => (Char.pull_bijective hb).1 (e.trans (pull_res h₁ h₀ hb χ).symm)⟩

theorem sp_pull_comm {V' S₁' S₀' : Scheme.{0}} {G' : Over V'} [GrpObj G'] [IsCommMonObj G']
    {G₁' : Over S₁'} [GrpObj G₁'] [IsCommMonObj G₁'] {G₀' : Over S₀'} [GrpObj G₀'] [IsCommMonObj G₀']
    {f₁' : S₁' ⟶ V'} {f₀' : S₀' ⟶ V'} {φ₁' : G₁'.left ⟶ G'.left} {φ₀' : G₀'.left ⟶ G'.left}
    (h₁' : IsGrpPullback G₁' G' f₁' φ₁') (h₀' : IsGrpPullback G₀' G' f₀' φ₀')
    (hb' : Function.Bijective (Cochar.pull h₁')) {v : V' ⟶ V} {s₁ : S₁' ⟶ S₁} {s₀ : S₀' ⟶ S₀}
    {ψ : G'.left ⟶ G.left} {ψ₁ : G₁'.left ⟶ G₁.left} {ψ₀ : G₀'.left ⟶ G₀.left}
    (k : IsGrpPullback G' G v ψ) (k₁ : IsGrpPullback G₁' G₁ s₁ ψ₁) (k₀ : IsGrpPullback G₀' G₀ s₀ ψ₀)
    (e₁ : f₁' ≫ v = s₁ ≫ f₁) (e₀ : f₀' ≫ v = s₀ ≫ f₀) (c₁ : φ₁' ≫ ψ = ψ₁ ≫ φ₁) (c₀ : φ₀' ≫ ψ = ψ₀ ≫ φ₀)
    (l : Cochar G₁) :
    sp h₁' h₀' hb' (Cochar.pull k₁ l) = Cochar.pull k₀ (sp h₁ h₀ hb l) := by
  obtain ⟨l, rfl⟩ := hb.2 l
  rw [sp_pull, Cochar.pull_pull k₁ h₁ (h₁'.comp k) e₁ c₁, Cochar.pull_pull k₀ h₀ (h₀'.comp k) e₀ c₀,
    Cochar.pull_comp h₁' k, Cochar.pull_comp h₀' k, sp_pull]

theorem pull_res_comm {V' S₁' S₀' : Scheme.{0}} {G' : Over V'} [GrpObj G'] [IsCommMonObj G']
    {G₁' : Over S₁'} [GrpObj G₁'] [IsCommMonObj G₁'] {G₀' : Over S₀'} [GrpObj G₀'] [IsCommMonObj G₀']
    {f₁' : S₁' ⟶ V'} {f₀' : S₀' ⟶ V'} {φ₁' : G₁'.left ⟶ G'.left} {φ₀' : G₀'.left ⟶ G'.left}
    (h₁' : IsGrpPullback G₁' G' f₁' φ₁') (h₀' : IsGrpPullback G₀' G' f₀' φ₀')
    (hb' : Function.Bijective (Cochar.pull h₁')) {v : V' ⟶ V} {s₁ : S₁' ⟶ S₁} {s₀ : S₀' ⟶ S₀}
    {ψ : G'.left ⟶ G.left} {ψ₁ : G₁'.left ⟶ G₁.left} {ψ₀ : G₀'.left ⟶ G₀.left}
    (k : IsGrpPullback G' G v ψ) (k₁ : IsGrpPullback G₁' G₁ s₁ ψ₁) (k₀ : IsGrpPullback G₀' G₀ s₀ ψ₀)
    (e₁ : f₁' ≫ v = s₁ ≫ f₁) (e₀ : f₀' ≫ v = s₀ ≫ f₀) (c₁ : φ₁' ≫ ψ = ψ₁ ≫ φ₁) (c₀ : φ₀' ≫ ψ = ψ₀ ≫ φ₀)
    (χ : Char G₀') :
    Char.pull k₁ (res h₁' h₀' hb' χ) = res h₁ h₀ hb (Char.pull k₀ χ) :=
  AddMonoidHom.ext fun l =>
    congrArg χ (sp_pull_comm h₁ h₀ hb h₁' h₀' hb' k k₁ k₀ e₁ e₀ c₁ c₀ l)

theorem pull_bijective_of_torus {Y : Type} [AddCommGroup Y] (j : splitTorus V Y ⟶ G) [IsMonHom j]
    (hj : Function.Surjective (ofTorus (pullTorus h₁ j))) (hi : Function.Injective (Cochar.pull h₁)) :
    Function.Bijective (Cochar.pull h₁) :=
  ⟨hi, fun l => by
    obtain ⟨m, rfl⟩ := hj l
    exact ⟨ofTorus j m, pull_ofTorus h₁ j m⟩⟩

theorem res_charEquivOfTorus {X Y : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (j : splitTorus V Y ⟶ G) [IsMonHom j]
    (hj : Function.Bijective (ofTorus (pullTorus h₁ j))) (i : splitTorus S₀ X ⟶ G₀) [IsMonHom i]
    (hi : Function.Bijective (ofTorus i)) (r : X →+ Y) (e : pullTorus h₀ j = torusMap S₀ r ≫ i) (x : X) :
    res h₁ h₀ hb (charEquivOfTorus i hi x) = charEquivOfTorus _ hj (r x) :=
  (eq_charEquivOfTorus_iff _ hj _ _).2 fun l => by
    have k : ofTorus (pullTorus h₀ j) l = ofTorus i (l.comp r) :=
      Cochar.ext (by rw [ofTorus_val, ofTorus_val, e, torusCochar_comp, Category.assoc])
    rw [res_apply, ← pull_ofTorus, sp_pull, pull_ofTorus, k, charEquivOfTorus_apply]
    rfl

end Spec

section SpecTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V S₁ S₀ : Scheme.{0}}
  {t : SAB H V} {t₁ : SAB H S₁} {t₀ : SAB H S₀} {f₁ : S₁ ⟶ V} {f₀ : S₀ ⟶ V}

def CocharOf.sp (m₁ : SABMap t₁ t f₁) (m₀ : SABMap t₀ t f₀) (hb : Function.Bijective (CocharOf.pull m₁)) :
    CocharOf t₁ →ₗ[𝓞 E] CocharOf t₀ where
  toFun l := TorusPart.sp m₁.cart m₀.cart hb l
  map_add' := map_add (TorusPart.sp m₁.cart m₀.cart hb)
  map_smul' a l := by
    obtain ⟨l, rfl⟩ := hb.2 l
    rw [← map_smul]
    exact (sp_pull m₁.cart m₀.cart hb _).trans (((CocharOf.pull m₀).map_smul a l).trans
      (congrArg (fun z : CocharOf t₀ => a • z) (sp_pull m₁.cart m₀.cart hb l).symm))

theorem CocharOf.sp_apply (m₁ : SABMap t₁ t f₁) (m₀ : SABMap t₀ t f₀)
    (hb : Function.Bijective (CocharOf.pull m₁)) (l : CocharOf t₁) :
    CocharOf.sp m₁ m₀ hb l = TorusPart.sp m₁.cart m₀.cart hb l := rfl

def CharOf.res (m₁ : SABMap t₁ t f₁) (m₀ : SABMap t₀ t f₀) (hb : Function.Bijective (CocharOf.pull m₁)) :
    CharOf t₀ →ₗ[𝓞 E] CharOf t₁ where
  toFun χ := TorusPart.res m₁.cart m₀.cart hb χ
  map_add' := map_add (TorusPart.res m₁.cart m₀.cart hb)
  map_smul' a χ := CharOf.ext fun l => congrArg χ ((CocharOf.sp m₁ m₀ hb).map_smul (H.bar a) l).symm

@[simp] theorem CharOf.res_apply (m₁ : SABMap t₁ t f₁) (m₀ : SABMap t₀ t f₀)
    (hb : Function.Bijective (CocharOf.pull m₁)) (χ : CharOf t₀) (l : CocharOf t₁) :
    CharOf.res m₁ m₀ hb χ l = χ (CocharOf.sp m₁ m₀ hb l) := rfl

theorem CharOf.pull_res (m₁ : SABMap t₁ t f₁) (m₀ : SABMap t₀ t f₀)
    (hb : Function.Bijective (CocharOf.pull m₁)) (χ : CharOf t₀) :
    CharOf.pull m₁ (CharOf.res m₁ m₀ hb χ) = CharOf.pull m₀ χ :=
  TorusPart.pull_res m₁.cart m₀.cart hb χ

end SpecTriple

theorem charEquivSplitTorus_id [ConnectedSpace S] (n : ℤ) :
    charEquivSplitTorus S (ULift.{0} ℤ) (ULift.up n) ⟨𝟙 (Gm S), inferInstance⟩ = n := by
  have e : (⟨𝟙 (Gm S), inferInstance⟩ : Cochar (Gm S)) =
      ofTorus (𝟙 _) (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom :=
    Cochar.ext ((Category.comp_id _).trans SplitTorus.torusMap_id).symm
  exact (congrArg _ e).trans (charEquivOfTorus_apply _ _ _ _)

example [ConnectedSpace S] : Nontrivial (Char (Gm S)) :=
  (charEquivSplitTorus S (ULift.{0} ℤ)).injective.nontrivial

theorem res_splitTorus {V S₁ S₀ : Scheme.{0}} [ConnectedSpace V] [ConnectedSpace S₁] [ConnectedSpace S₀]
    (f₁ : S₁ ⟶ V) (f₀ : S₀ ⟶ V) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ hb : Function.Bijective (Cochar.pull (SplitTorus.isGrpPullback_bcMap f₁ X)), ∀ x : X,
      res _ (SplitTorus.isGrpPullback_bcMap f₀ X) hb (charEquivSplitTorus S₀ X x) =
        charEquivSplitTorus S₁ X x := by
  have k : ∀ {T : Scheme.{0}} (f : T ⟶ V) (l : X →+ ℤ),
      Cochar.pull (SplitTorus.isGrpPullback_bcMap f X) (ofTorus (𝟙 _) l) = ofTorus (𝟙 _) l :=
    fun f l => pull_ofTorus_of_left _ _ _ (by simp) l
  have hb : Function.Bijective (Cochar.pull (SplitTorus.isGrpPullback_bcMap f₁ X)) := by
    refine (Function.Bijective.of_comp_iff _ ofTorus_id_bijective).1 ?_
    rw [show Cochar.pull (SplitTorus.isGrpPullback_bcMap f₁ X) ∘ ofTorus (𝟙 _) = ofTorus (𝟙 _) from
      funext (k f₁)]
    exact ofTorus_id_bijective
  refine ⟨hb, fun x => (eq_charEquivOfTorus_iff _ ofTorus_id_bijective _ _).2 fun l => ?_⟩
  rw [res_apply, ← k f₁, sp_pull, k]
  exact charEquivOfTorus_apply _ _ _ _

theorem exists_rank_drop : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E)
    (t : SAB H (Sp (PowerSeries ℂ))) (t₁ : SAB H (Sp (FractionRing (PowerSeries ℂ)))) (t₀ : SAB H (Sp ℂ))
    (m₁ : SABMap t₁ t (spMap (algebraMap _ _))) (_ : SABMap t₀ t (spMap PowerSeries.constantCoeff)),
    Nontrivial (CharOf t₀) ∧ Nontrivial (CocharOf t₀) ∧ Subsingleton (CocharOf t₁) ∧
      Subsingleton (CharOf t₁) ∧ Function.Bijective (CocharOf.pull m₁) := by
  obtain ⟨⟨E, _, _, _, H, t, P, -, hn⟩, -⟩ := Inhab.exists_unif_nontrivial_torus
  obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt (Out.jK (PowerSeries ℂ)) t
  obtain ⟨_, _, _, _, _, m₀, -⟩ :=
    sabPull Out.proved_CubePullSt (spMap (PowerSeries.constantCoeff (R := ℂ))) t
  have hρ : ∀ x ∈ Ideal.span {(PowerSeries.X : PowerSeries ℂ)}, PowerSeries.constantCoeff x = 0 :=
    fun x hx => PowerSeries.X_dvd_iff.1 (Ideal.mem_span_singleton.1 hx)
  have h₀ := (PELUnif.charEquivOfKer P hρ m₀).injective.nontrivial
  have hp : IsProper ((Over.pullback (Out.jK (PowerSeries ℂ))).obj t.G).hom := by
    have := P.A.isAb.proper
    have := isIso_inv_left P.U.gen.symm
    rw [← Over.w P.U.gen.symm.inv]
    infer_instance
  have h₁ := subsingleton_cochar_of_isProper ((Over.pullback (Out.jK (PowerSeries ℂ))).obj t.G)
  have triv : ∀ {T : Scheme.{0}} (u : SAB H T), Subsingleton (CocharOf u) → Subsingleton (CharOf u) :=
    fun u _ => ⟨fun χ χ' => CharOf.ext fun l => by rw [Subsingleton.elim l 0, map_zero, map_zero]⟩
  refine ⟨E, _, _, _, H, t, _, _, m₁, m₀, h₀, ?_, h₁, triv _ h₁, ?_, fun l => ⟨0, h₁.elim _ _⟩⟩
  · by_contra c
    exact not_subsingleton_iff_nontrivial.2 h₀ (triv _ (not_nontrivial_iff_subsingleton.1 c))
  · obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))
    have := t.semi.separated
    exact Cochar.pull_injective m₁.cart

end GlobalTheory.TorusPart
