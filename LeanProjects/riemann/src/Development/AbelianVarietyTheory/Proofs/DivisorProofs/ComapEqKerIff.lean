import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

def IsFinFlatRk {X Y : Scheme.{0}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = r

lemma IsFinFlatRk.of_isPullback {P X Y T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ Y}
    {g : T ⟶ Y} (h : IsPullback fst snd f g) {r : ℕ} (hf : IsFinFlatRk f r) : IsFinFlatRk snd r := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h h1,
    MorphismProperty.of_isPullback (P := @Flat) h h2, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g h y, h3]

lemma IsFinFlatRk.iso_comp {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y} {r : ℕ}
    (hf : IsFinFlatRk f r) : IsFinFlatRk (e ≫ f) r :=
  IsFinFlatRk.of_isPullback (IsPullback.of_horiz_isIso (fst := e) (g := 𝟙 Y) ⟨by simp⟩) hf

lemma isPullback_comap {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f))
      f I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

variable {S Z : Scheme.{0}} (z : Z ⟶ S)

def bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    pullback z k ⟶ pullback z g :=
  pullback.map z k z g (𝟙 Z) c (𝟙 S) (by simp) (by rw [Category.comp_id, w])

lemma isPullback_bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    IsPullback (bc z c g k w) (pullback.snd z k) (pullback.snd z g) c := by
  subst w
  refine IsPullback.of_right ?_ (by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]) (IsPullback.of_hasPullback z g)
  have e : bc z c g (c ≫ g) rfl ≫ pullback.fst z g = pullback.fst z (c ≫ g) := by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]
  rw [e]
  exact IsPullback.of_hasPullback z (c ≫ g)

lemma bc_id {T : Scheme.{0}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) : bc z (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [bc]

lemma bc_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (m : R ⟶ S)
    (w : a ≫ g = k) (w' : b ≫ k = m) (w'' : (b ≫ a) ≫ g = m) :
    bc z (b ≫ a) g m w'' = bc z b k m w' ≫ bc z a g k w := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

variable (r : ℕ)

abbrev HIdeal {T : Scheme.{0}} (g : T ⟶ S) : Type :=
  {I : (pullback z g).IdealSheafData // IsFinFlatRk (I.subschemeι ≫ pullback.snd z g) r}

abbrev HPt (T : Scheme.{0}) : Type := Σ g : T ⟶ S, HIdeal z r g

variable {z r}

def HIdeal.pull {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HIdeal z r k :=
  ⟨I.1.comap (bc z c g k w), IsFinFlatRk.of_isPullback
    ((isPullback_comap I.1 (bc z c g k w)).flip.paste_vert (isPullback_bc z c g k w)) I.2⟩

def HPt.map {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) : HPt z r T' :=
  ⟨c ≫ x.1, x.2.pull c rfl⟩

lemma HPt.map_mk {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HPt.map c ⟨g, I⟩ = ⟨k, I.pull c w⟩ := by
  subst w; rfl

lemma HPt.mk_eq_mk_iff {T : Scheme.{0}} {g : T ⟶ S} (I J : HIdeal z r g) :
    (⟨g, I⟩ : HPt z r T) = ⟨g, J⟩ ↔ I.1 = J.1 := by
  rw [Sigma.mk.inj_iff, heq_iff_eq, Subtype.ext_iff]
  simp

lemma HPt.map_eq_mk_iff {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) {k : T' ⟶ S}
    (w : c ≫ x.1 = k) (J : HIdeal z r k) :
    HPt.map c x = ⟨k, J⟩ ↔ x.2.1.comap (bc z c x.1 k w) = J.1 := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk c w, HPt.mk_eq_mk_iff]
  rfl

lemma HPt.map_id {T : Scheme.{0}} (x : HPt z r T) : HPt.map (𝟙 T) x = x := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (𝟙 T) (Category.id_comp g), HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (𝟙 T) g g _) = I.1
  rw [bc_id, Scheme.IdealSheafData.comap_id]

lemma HPt.map_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (x : HPt z r T) :
    HPt.map (b ≫ a) x = HPt.map b (HPt.map a x) := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (b ≫ a) (Category.assoc b a g), HPt.map_mk a rfl, HPt.map_mk b rfl, HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (b ≫ a) g _ _) = (I.1.comap (bc z a g _ rfl)).comap (bc z b (a ≫ g) _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, bc_comp z b a g (a ≫ g) (b ≫ a ≫ g) rfl rfl]

variable (z r)

def hilbFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := HPt z r T.unop
  map c := TypeCat.ofHom (HPt.map c.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x => HPt.map_id x
  map_comp a b := ConcreteCategory.hom_ext _ _ fun x => HPt.map_comp _ _ x

def hilbProj : hilbFunctor z r ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun x => x.1

variable {z r}

lemma IsFinFlatRk.ker_subschemeι {T V : Scheme.{0}} {g : T ⟶ S} (v : V ⟶ pullback z g)
    [IsClosedImmersion v] (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) :
    IsFinFlatRk (v.ker.subschemeι ≫ pullback.snd z g) r := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc]
  exact hv.iso_comp _

def mkPt {T V : Scheme.{0}} (g : T ⟶ S) (v : V ⟶ pullback z g) [IsClosedImmersion v]
    (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) : HPt z r T :=
  ⟨g, v.ker, hv.ker_subschemeι v⟩

theorem comap_eq_ker_iff {X Y V : Scheme.{0}} (m : X ⟶ Y) (I : Y.IdealSheafData) (v : V ⟶ X)
    [IsClosedImmersion v] : I.comap m = v.ker ↔ ∃ w : V ⟶ I.subscheme, IsPullback v w m I.subschemeι := by
  constructor
  · intro h
    have H : I.subschemeι.ker ≤ (v ≫ m).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift I.subschemeι (v ≫ m) H,
      isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_⟩
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  · rintro ⟨w, hP⟩
    rw [← hP.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end GlobalTheory.HilbGlue
