import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Raynaud

section Formal

variable {R : Type} [CommRing R] (I : Ideal R)

def IsFormalIso (G Gt : Over (Sp R)) [GrpObj G] [GrpObj Gt]
    (ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left) : Prop :=
  (∀ e, IsGrpPullback (thickObj R I e G) Gt (thick R I e) (ψ e)) ∧ ∀ e, thickMap R I e G ≫ ψ (e + 1) = ψ e

def IsExtension (G Gt : Over (Sp R)) [GrpObj G] [GrpObj Gt]
    (ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left) : Prop :=
  IsSemiAbelian Gt ∧
    (∃ (X : Type) (_ : AddCommGroup X), Module.Free ℤ X ∧ Module.Finite ℤ X ∧ Nonempty (UU.TQ Gt X)) ∧
    IsFormalIso I G Gt ψ

theorem isFormalIso_refl (G : Over (Sp R)) [GrpObj G] :
    IsFormalIso I G G fun e => pullback.fst G.hom (thick R I e) :=
  ⟨fun e => isGrpPullback_pullback G (thick R I e), fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _)⟩

theorem isExtension_refl (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (Q : UU.TQ G X) :
    IsExtension I G G fun e => pullback.fst G.hom (thick R I e) :=
  ⟨hG, ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q⟩⟩, isFormalIso_refl I G⟩

variable {I}

theorem IsFormalIso.baseChange {G Gt : Over (Sp R)} [GrpObj G] [GrpObj Gt]
    {ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left} (h : IsFormalIso I G Gt ψ)
    {R' : Type} [CommRing R'] {I' : Ideal R'} (φ : R →+* R') (hI : I ≤ I'.comap φ)
    {G' Gt' : Over (Sp R')} [GrpObj G'] [GrpObj Gt'] {F : G'.left ⟶ G.left} {Ft : Gt'.left ⟶ Gt.left}
    (hF : IsGrpPullback G' G (spMap φ) F) (hFt : IsGrpPullback Gt' Gt (spMap φ) Ft) :
    ∃ ψ', IsFormalIso I' G' Gt' ψ' ∧ ∀ e (u : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left),
      u ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫ F → ψ' e ≫ Ft = u ≫ ψ e := by
  have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := fun e =>
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  let s : ∀ e : ℕ, Sp (R' ⧸ I' ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) := fun e =>
    spMap (Ideal.quotientMap _ φ (hle e))
  have hs : ∀ e, s e ≫ thick R I e = thick R' I' e ≫ spMap φ := fun e => by
    simp only [s, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have mono : ∀ e, Mono (pullback.fst G.hom (thick R I e)) := fun e => by
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hu : ∀ e, ∃ u : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left,
      u ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫ F ∧
      u ≫ (thickObj R I e G).hom = (thickObj R' I' e G').hom ≫ s e := fun e =>
    (isGrpPullback_pullback G (thick R I e)).1.exists_lift _ _ (by
      rw [Category.assoc, Category.assoc, hs, hF.1.w, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ spMap φ) pullback.condition)
  choose u hu₁ hu₂ using hu
  have hg : ∀ e, IsGrpPullback (thickObj R' I' e G') Gt (thick R' I' e ≫ spMap φ) (u e ≫ ψ e) := fun e =>
    (((isGrpPullback_pullback G (thick R I e)).cancel
      (((isGrpPullback_pullback G' (thick R' I' e)).comp hF).congr (hs e).symm (hu₁ e).symm) (hu₂ e)).comp
      (h.1 e)).congr (hs e) rfl
  have hv : ∀ e, ∃ v : (thickObj R' I' e G').left ⟶ Gt'.left, v ≫ Ft = u e ≫ ψ e ∧
      v ≫ Gt'.hom = (thickObj R' I' e G').hom ≫ thick R' I' e := fun e =>
    hFt.1.exists_lift _ _ (by rw [(hg e).1.w, Category.assoc])
  choose v hv₁ hv₂ using hv
  refine ⟨v, ⟨fun e => hFt.cancel ((hg e).congr rfl (hv₁ e).symm) (hv₂ e), fun e => ?_⟩, fun e w hw => ?_⟩
  · have k : thickMap R' I' e G' ≫ u (e + 1) = u e ≫ thickMap R I e G := by
      have := mono (e + 1)
      rw [← cancel_mono (pullback.fst G.hom (thick R I (e + 1))), Category.assoc, Category.assoc, hu₁,
        (isFormalIso_refl I G).2 e, hu₁, ← Category.assoc, (isFormalIso_refl I' G').2 e]
    refine hFt.1.hom_ext ?_ ?_
    · rw [Category.assoc, hv₁, hv₁, ← Category.assoc, k, Category.assoc, h.2]
    · rw [Category.assoc, hv₂, hv₂, ← thickTrans_comp R' I' e, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ thick R' I' (e + 1)) (pullback.lift_snd _ _ _)
  · have := mono e
    rw [hv₁, (cancel_mono _).1 (hw.trans (hu₁ e).symm)]

theorem IsExtension.baseChange {G Gt : Over (Sp R)} [GrpObj G] [GrpObj Gt]
    {ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left} (h : IsExtension I G Gt ψ)
    {R' : Type} [CommRing R'] {I' : Ideal R'} (φ : R →+* R') (hI : I ≤ I'.comap φ)
    {G' : Over (Sp R')} [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (spMap φ) F) :
    ∃ ψ', IsExtension I' G' ((Over.pullback (spMap φ)).obj Gt) ψ' ∧
      ∀ e (u : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left),
        u ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫ F →
          ψ' e ≫ pullback.fst Gt.hom (spMap φ) = u ≫ ψ e := by
  obtain ⟨h₁, ⟨X, _, h₂, h₃, ⟨Q⟩⟩, h₄⟩ := h
  have hFt := isGrpPullback_pullback Gt (spMap φ)
  obtain ⟨ψ', h₅, h₆⟩ := h₄.baseChange φ hI hF hFt
  obtain ⟨Q', -⟩ := UU.exists_tq_baseChange _ _ _ X _ _ _ hFt Q
  exact ⟨ψ', ⟨IsSemiAbelian.pullback _ Gt h₁, ⟨X, inferInstance, h₂, h₃, ⟨Q'⟩⟩, h₅⟩, h₆⟩

end Formal

section Parts

variable {S : Scheme.{0}}

def LiesIn {H G : Over S} (j : H ⟶ G) {Y : Scheme.{0}} (x : Y ⟶ G.left) : Prop :=
  ∃ h : Y ⟶ H.left, h ≫ j.left = x

structure IsFiniteFlatSubgroup {H G : Over S} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop where
  closed : IsClosedImmersion j.left
  finite : IsFinite H.hom
  flat : Flat H.hom
  one_mem : LiesIn j (η[G]).left
  mul_mem : ∀ (Y : Over S) (a b : Y ⟶ H), LiesIn j ((a ≫ j) * (b ≫ j)).left
  pow_eq_one : j ^ n = 1

variable {V : Type} [CommRing V]

def IsFinitePart {H G : Over (Sp V)} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop :=
  IsFiniteFlatSubgroup n j ∧ ∃ (Ω : Type) (_ : Field Ω) (p : V →+* Ω), IsLocalHom p ∧
    ∀ (Y : Over (Sp Ω)) (y : Y ⟶ (Over.pullback (spMap p)).obj G),
      LiesIn j (y.left ≫ pullback.fst G.hom (spMap p)) ↔ y ^ n = 1

def IsTorusPart {H G : Over (Sp V)} [GrpObj G] (n : ℕ) (j : H ⟶ G) : Prop :=
  IsFiniteFlatSubgroup n j ∧ ∃ (Ω : Type) (_ : Field Ω) (p : V →+* Ω), IsLocalHom p ∧
    ∃ E : TorusExtension ((Over.pullback (spMap p)).obj G),
      ∀ (Y : Over (Sp Ω)) (y : Y ⟶ (Over.pullback (spMap p)).obj G),
        LiesIn j (y.left ≫ pullback.fst G.hom (spMap p)) ↔ y ^ n = 1 ∧ ∃ t, t ≫ E.i = y

def PairsToOne {A A' : Over S} [GrpObj A] [GrpObj A'] (P : LB (A ⊗ A').left) (n : ℕ) {T : Over S}
    (x : T ⟶ A) (y : T ⟶ A') : Prop :=
  WeilIs (A ⊗ A') P (n : ℤ) (lift x 1) (lift 1 y) 1

theorem liesIn_torsion_iff (G : Over S) [GrpObj G] (n : ℕ) {Y : Over S} (x : Y ⟶ G) :
    LiesIn (torsion.ι G n) x.left ↔ x ^ n = 1 := by
  have e : ∀ {Z : Over S} (z : Z ⟶ G), z ≫ mulN G n = z ^ n := fun z => by
    rw [SplitTorus.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  constructor
  · rintro ⟨h, hh⟩
    let h' : Y ⟶ torsion G n := Over.homMk h (by rw [← Over.w (torsion.ι G n), ← Category.assoc, hh, Over.w])
    have : h' ≫ torsion.ι G n = x := Over.OverMorphism.ext hh
    let s : torsion G n ⟶ 𝟙_ (Over S) := pullback.snd (mulN G n) η[G]
    have c : torsion.ι G n ≫ mulN G n = s ≫ η[G] := pullback.condition
    rw [← e, ← this, Category.assoc, c, ← Category.assoc, Hom.one_def, toUnit_unique (h' ≫ s) (toUnit Y)]
  · intro hx
    let l : Y ⟶ torsion G n := pullback.lift x (toUnit Y) ((e x).trans hx)
    have c : l ≫ torsion.ι G n = x := pullback.lift_fst _ _ _
    exact ⟨l.left, congrArg (fun q => q.left) c⟩

theorem pow_eq_one_iff_of_isGrpPullback {S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {Y : Over S'} (y : Y ⟶ G') (n : ℕ) :
    pushPt h.1.w y ^ n = 1 ↔ y ^ n = 1 := by
  let m : (Y ⟶ G') →* (Over.mk (Y.hom ≫ f) ⟶ G) := MonoidHom.mk' (fun z => pushPt h.1.w z) fun a b =>
    Over.OverMorphism.ext (h.2 Y a b _ _ rfl rfl).symm
  have hm : Function.Injective m := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  show m y ^ n = 1 ↔ _
  rw [← map_pow, map_eq_one_iff m hm]

theorem isFiniteFlatSubgroup_torsion (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] (n : ℕ)
    (h₁ : IsFinite (torsion G n).hom) (h₂ : Flat (torsion G n).hom) : IsFiniteFlatSubgroup n (torsion.ι G n) := by
  have k : ∀ {Y : Over S} (a : Y ⟶ torsion G n), (a ≫ torsion.ι G n) ^ n = 1 := fun a =>
    (liesIn_torsion_iff G n _).1 ⟨a.left, rfl⟩
  refine ⟨?_, h₁, h₂, (liesIn_torsion_iff G n _).2 ?_, fun Y a b => (liesIn_torsion_iff G n _).2 ?_, ?_⟩
  · have : IsFinite ((torsion.ι G n).left ≫ G.hom) := by rw [Over.w]; exact h₁
    have : IsFinite (torsion.ι G n).left := IsFinite.of_comp _ G.hom
    have : Mono (η[G]) := ⟨fun a b _ => toUnit_unique a b⟩
    have : Mono (torsion.ι G n) := inferInstanceAs (Mono (pullback.fst _ _))
    have : Mono (torsion.ι G n).left := inferInstanceAs (Mono ((Over.forget S).map (torsion.ι G n)))
    exact (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, inferInstance⟩
  · have : η[G] = (1 : 𝟙_ (Over S) ⟶ G) := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this, one_pow]
  · rw [mul_pow, k, k, _root_.mul_one]
  · simpa using k (𝟙 _)

theorem liesIn_torsion_fibre {S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) {Y : Over S'}
    (y : Y ⟶ (Over.pullback f).obj G) :
    LiesIn (torsion.ι G n) (y.left ≫ pullback.fst G.hom f) ↔ y ^ n = 1 :=
  (liesIn_torsion_iff G n (pushPt (isGrpPullback_pullback G f).1.w y)).trans
    (pow_eq_one_iff_of_isGrpPullback (isGrpPullback_pullback G f) y n)

theorem isFinitePart_torsion [IsLocalRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom]
    (n : ℕ) (h₁ : IsFinite (torsion G n).hom) (h₂ : Flat (torsion G n).hom) : IsFinitePart n (torsion.ι G n) :=
  ⟨isFiniteFlatSubgroup_torsion G n h₁ h₂, _, inferInstance, IsLocalRing.residue V, inferInstance,
    fun _ y => liesIn_torsion_fibre _ G n y⟩

theorem parts_splitTorus [IsLocalRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {n : ℕ} (hn : n ≠ 0) :
    IsFinitePart n (torsion.ι (splitTorus (Sp V) X) n) ∧ IsTorusPart n (torsion.ι (splitTorus (Sp V) X) n) := by
  have a₁ := Diag.isFinite_mulN (Sp V) X hn
  have a₂ := Diag.flat_mulN (Sp V) X hn
  have sq := (IsPullback.of_hasPullback (mulN (splitTorus (Sp V) X) n) η[splitTorus (Sp V) X]).map (Over.forget _)
  have e : (torsion (splitTorus (Sp V) X) n).hom =
      (pullback.snd (mulN (splitTorus (Sp V) X) n) η[splitTorus (Sp V) X]).left :=
    ((Category.comp_id _).symm.trans (Over.w _)).symm
  have h₁ : IsFinite (torsion (splitTorus (Sp V) X) n).hom := by
    rw [e]; exact MorphismProperty.of_isPullback sq a₁
  have h₂ : Flat (torsion (splitTorus (Sp V) X) n).hom := by
    rw [e]; exact MorphismProperty.of_isPullback sq a₂
  refine ⟨isFinitePart_torsion _ n h₁ h₂, isFiniteFlatSubgroup_torsion _ n h₁ h₂, _, inferInstance,
    IsLocalRing.residue V, inferInstance, Diag.torusExtension _ X _, fun Y y => ?_⟩
  rw [liesIn_torsion_fibre]
  exact ⟨fun h => ⟨h, y ≫ (Diag.baseChangeIso _ X).hom, (Category.assoc _ _ _).trans
    ((congrArg (y ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))⟩, fun h => h.1⟩

theorem henselianLocalRing_of_isAdicComplete [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] :
    HenselianLocalRing V where
  is_henselian f hf a h₁ h₂ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal V) f hf a h₁ (h₂.map _)

end Parts

end GlobalTheory.Raynaud

namespace GlobalTheory.Published

open GlobalTheory.Raynaud IsLocalRing

def RaynaudExtension.Exists : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
      ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (ψ : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G).left ⟶ Gt.left),
        IsExtension (maximalIdeal R) G Gt ψ

def RaynaudExtension.Functorial : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G G' Gt Gt' : Over (Sp R)) [GrpObj G] [GrpObj G'] [GrpObj Gt] [GrpObj Gt'],
      IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) →
      IsSemiAbelian G' → IsProper (pullback.snd G'.hom (jK R)) →
    ∀ (ψ : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G).left ⟶ Gt.left)
      (ψ' : ∀ e : ℕ, (thickObj R (maximalIdeal R) e G').left ⟶ Gt'.left),
      IsExtension (maximalIdeal R) G Gt ψ → IsExtension (maximalIdeal R) G' Gt' ψ' →
    ∀ f : G ⟶ G', IsMonHom f → ∃! ft : Gt ⟶ Gt', IsMonHom ft ∧
      ∀ e, ψ e ≫ ft.left = ((Over.pullback (thick R (maximalIdeal R) e)).map f).left ≫ ψ' e

def GrothendieckOrthogonality : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [HenselianLocalRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (G G' : Over (Sp V)) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G'.left),
      IsAbelianScheme A → IsAbelianScheme A' →
      IsGrpPullback A G (spMap (algebraMap V K)) φ → IsGrpPullback A' G' (spMap (algebraMap V K)) φ' →
    ∀ P : LB (A ⊗ A').left, AbDual.IsDual A A' P →
    ∀ (l r : ℕ), l.Prime → (l : K) ≠ 0 →
    ∀ (H H' : Over (Sp V)) (j : H ⟶ G) (j' : H' ⟶ G'), IsTorusPart (l ^ r) j → IsFinitePart (l ^ r) j' →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω],
      (∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l ^ r = 1 →
        (LiesIn j (x.left ≫ φ) ↔
          ∀ y : Over.mk (spMap (algebraMap K Ω)) ⟶ A', LiesIn j' (y.left ≫ φ') → PairsToOne P (l ^ r) x y)) ∧
      ∀ y : Over.mk (spMap (algebraMap K Ω)) ⟶ A', y ^ l ^ r = 1 →
        (LiesIn j' (y.left ≫ φ') ↔
          ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, LiesIn j (x.left ≫ φ) → PairsToOne P (l ^ r) x y)

def RaynaudExtension : Prop :=
  RaynaudExtension.Exists ∧ RaynaudExtension.Functorial ∧ GrothendieckOrthogonality

end GlobalTheory.Published
