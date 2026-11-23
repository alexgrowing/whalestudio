import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.KerSubgroup
open SplitPull

theorem exists_agree_locus (X : Scheme.{0}) (N : Type) (v w : N → Γ(X, ⊤)) :
    ∃ (Z : Scheme.{0}) (m : Z ⟶ X), IsClosedImmersion m ∧ (∀ n, m.appTop.hom (v n) = m.appTop.hom (w n)) ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X), (∀ n, f.appTop.hom (v n) = f.appTop.hom (w n)) → ∃ z, z ≫ m = f := by
  let A : Over X := Over.mk (𝔸(N; X) ↘ X)
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (𝔸(N; X) ↘ X))
  let hv : Over.mk (𝟙 X) ⟶ A := Over.homMk (AffineSpace.homOfVector (𝟙 X) v) (AffineSpace.homOfVector_over _ _)
  let hw : Over.mk (𝟙 X) ⟶ A := Over.homMk (AffineSpace.homOfVector (𝟙 X) w) (AffineSpace.homOfVector_over _ _)
  have key : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (u : N → Γ(X, ⊤)) (n : N),
      (f ≫ AffineSpace.homOfVector (𝟙 X) u).appTop (AffineSpace.coord X n) = f.appTop.hom (u n) := by
    intro Y f u n
    rw [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord]
    rfl
  refine ⟨(equalizer hv hw).left, (equalizer.ι hv hw).left, inferInstance, fun n => ?_, fun Y f hf => ?_⟩
  · have e : (equalizer.ι hv hw).left ≫ AffineSpace.homOfVector (𝟙 X) v =
        (equalizer.ι hv hw).left ≫ AffineSpace.homOfVector (𝟙 X) w :=
      congrArg CommaMorphism.left (equalizer.condition hv hw)
    rw [← key, ← key, e]
  · let f' : Over.mk f ⟶ Over.mk (𝟙 X) := Over.homMk f (Category.comp_id _)
    have e : f' ≫ hv = f' ≫ hw := by
      ext1
      change f ≫ AffineSpace.homOfVector (𝟙 X) v = f ≫ AffineSpace.homOfVector (𝟙 X) w
      refine AffineSpace.hom_ext (by simp) fun n => ?_
      rw [key, key, hf]
    exact ⟨(equalizer.lift f' e).left, congrArg CommaMorphism.left (equalizer.lift_ι f' e)⟩

def Rel {X Y : Scheme.{0}} (C : Charts X) (a : {i // C.wt i = C.c₀}) {d : ℕ} (j : Fin d → C.I)
    (k₁ k₂ k₃ e : Y ⟶ X) : Prop :=
  ∃ (h₁ : ⊤ ≤ k₁ ⁻¹ᵁ C.W a) (h₂ : ⊤ ≤ k₂ ⁻¹ᵁ C.W a) (h₃ : ⊤ ≤ k₃ ⁻¹ᵁ C.W a) (h : ⊤ ≤ e ⁻¹ᵁ C.W a),
    (∀ l, C.wt l = C.c₀ → (k₁.appLE _ ⊤ h₁).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l) ∧
      (k₂.appLE _ ⊤ h₂).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l) ∧
      (k₃.appLE _ ⊤ h₃).hom (C.r a l) = (e.appLE _ ⊤ h).hom (C.r a l)) ∧
    ∀ n, (k₁.appLE _ ⊤ h₁).hom (C.r a (j n)) * (k₂.appLE _ ⊤ h₂).hom (C.r a (j n)) =
      (k₃.appLE _ ⊤ h₃).hom (C.r a (j n)) * (e.appLE _ ⊤ h).hom (C.r a (j n))

theorem Rel.comp {X Y Y' : Scheme.{0}} {C : Charts X} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I}
    {k₁ k₂ k₃ e : Y ⟶ X} (H : Rel C a j k₁ k₂ k₃ e) (p : Y' ⟶ Y) :
    Rel C a j (p ≫ k₁) (p ≫ k₂) (p ≫ k₃) (p ≫ e) := by
  obtain ⟨h₁, h₂, h₃, h, H₁, H₂⟩ := H
  have g : ∀ k : Y ⟶ X, ⊤ ≤ k ⁻¹ᵁ C.W a → ⊤ ≤ (p ≫ k) ⁻¹ᵁ C.W a := fun k h => p.preimage_mono h
  have key : ∀ (k : Y ⟶ X) (h : ⊤ ≤ k ⁻¹ᵁ C.W a) (l : C.I),
      ((p ≫ k).appLE _ ⊤ (g k h)).hom (C.r a l) = p.appTop.hom ((k.appLE _ ⊤ h).hom (C.r a l)) :=
    fun k h l => (appTop_appLE p k _ rfl _ h _ _).symm
  refine ⟨g _ h₁, g _ h₂, g _ h₃, g _ h, fun l hl => ?_, fun n => ?_⟩
  · rw [key _ h₁, key _ h₂, key _ h₃, key _ h, (H₁ l hl).1, (H₁ l hl).2.1, (H₁ l hl).2.2]
    exact ⟨rfl, rfl, rfl⟩
  · rw [key _ h₁, key _ h₂, key _ h₃, key _ h, ← map_mul, ← map_mul, H₂]

theorem rel_pull {X X' Y : Scheme.{0}} (C : Charts X) (φ : X' ⟶ X) [IsAffineHom φ] (a : {i // C.wt i = C.c₀})
    {d : ℕ} (j : Fin d → C.I) (k₁ k₂ k₃ e : Y ⟶ X') :
    Rel (C.pull φ) a j k₁ k₂ k₃ e ↔ Rel C a j (k₁ ≫ φ) (k₂ ≫ φ) (k₃ ≫ φ) (e ≫ φ) := by
  have key : ∀ (k : Y ⟶ X') (h : ⊤ ≤ k ⁻¹ᵁ (C.pull φ).W a) (l : C.I),
      (k.appLE _ ⊤ h).hom ((C.pull φ).r a l) = ((k ≫ φ).appLE (C.W a) ⊤ h).hom (C.r a l) :=
    fun k h l => appLE_app k φ _ rfl _ h h _
  refine exists_congr fun h₁ => exists_congr fun h₂ => exists_congr fun h₃ => exists_congr fun h => ?_
  simp only [key]
  rfl

variable {S : Scheme.{0}} {H : Over S} [GrpObj H]

theorem exists_rep [IsAffine S] [LocallyOfFiniteType H.hom] (C : Charts H.left) (a : {i // C.wt i = C.c₀})
    {d : ℕ} (j : Fin d → C.I) (he : ⊤ ≤ eSec H ⁻¹ᵁ C.W a) :
    ∃ (Z : Over S) (k₁ k₂ k₃ : Z ⟶ H), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      Rel C a j k₁.left k₂.left k₃.left (1 : Z ⟶ H).left ∧
      ∀ (Y : Over S) (l₁ l₂ l₃ : Y ⟶ H), Rel C a j l₁.left l₂.left l₃.left (1 : Y ⟶ H).left →
        ∃ z : Y ⟶ Z, z ≫ k₁ = l₁ ∧ z ≫ k₂ = l₂ ∧ z ≫ k₃ = l₃ := by
  let W : Over S := Over.mk ((C.W a).ι ≫ H.hom)
  let inc : W ⟶ H := Over.homMk (C.W a).ι rfl
  have : IsAffine W.left := C.aff a
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType ((C.W a).ι ≫ H.hom))
  have : QuasiCompact W.hom := inferInstance
  let X : Over S := W ⊗ W ⊗ W
  have hX₁ : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (pullback.fst W.hom (pullback.fst W.hom W.hom ≫ W.hom) ≫ W.hom)
    infer_instance
  have hX₂ : QuasiCompact X.hom := by
    change QuasiCompact (pullback.fst W.hom (pullback.fst W.hom W.hom ≫ W.hom) ≫ W.hom)
    infer_instance
  have hinc : ∀ p : X ⟶ W, ⊤ ≤ (p ≫ inc).left ⁻¹ᵁ C.W a := fun p x _ => (p.left x).2
  have h1 : ⊤ ≤ (1 : X ⟶ H).left ⁻¹ᵁ C.W a := (toUnit X).left.preimage_mono he
  let p₁ : X ⟶ W := fst _ _
  let p₂ : X ⟶ W := snd _ _ ≫ fst _ _
  let p₃ : X ⟶ W := snd _ _ ≫ snd _ _
  let E (p : X ⟶ W) (l : C.I) := ((p ≫ inc).left.appLE _ ⊤ (hinc p)).hom (C.r a l)
  let E₀ (l : C.I) := ((1 : X ⟶ H).left.appLE _ ⊤ h1).hom (C.r a l)
  let J := {l // C.wt l = C.c₀}
  obtain ⟨Z, m, hm, hZ, hu⟩ := exists_agree_locus X.left (J ⊕ J ⊕ J ⊕ Fin d)
    (Sum.elim (fun l => E p₁ l.1) (Sum.elim (fun l => E p₂ l.1) (Sum.elim (fun l => E p₃ l.1)
      fun n => E p₁ (j n) * E p₂ (j n))))
    (Sum.elim (fun l => E₀ l.1) (Sum.elim (fun l => E₀ l.1) (Sum.elim (fun l => E₀ l.1)
      fun n => E p₃ (j n) * E₀ (j n))))
  have key : ∀ (Y : Over S) (f : Y ⟶ X),
      Rel C a j (f ≫ p₁ ≫ inc).left (f ≫ p₂ ≫ inc).left (f ≫ p₃ ≫ inc).left (1 : Y ⟶ H).left ↔
      ((∀ l : J, f.left.appTop.hom (E p₁ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      (∀ l : J, f.left.appTop.hom (E p₂ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      (∀ l : J, f.left.appTop.hom (E p₃ l.1) = f.left.appTop.hom (E₀ l.1)) ∧
      ∀ n, f.left.appTop.hom (E p₁ (j n) * E p₂ (j n)) = f.left.appTop.hom (E p₃ (j n) * E₀ (j n))) := by
    intro Y f
    have g : ∀ p : X ⟶ W, ⊤ ≤ (f ≫ p ≫ inc).left ⁻¹ᵁ C.W a := fun p => f.left.preimage_mono (hinc p)
    have g1 : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := (toUnit Y).left.preimage_mono he
    have e : ∀ p l, f.left.appTop.hom (E p l) = ((f ≫ p ≫ inc).left.appLE _ ⊤ (g p)).hom (C.r a l) :=
      fun p l => appTop_appLE _ _ _ rfl _ _ _ _
    have e₀ : ∀ l, f.left.appTop.hom (E₀ l) = ((1 : Y ⟶ H).left.appLE _ ⊤ g1).hom (C.r a l) :=
      fun l => appTop_appLE _ _ _ (by rw [← Over.comp_left, MonObj.comp_one]) _ _ _ _
    simp only [map_mul, e, e₀]
    constructor
    · rintro ⟨_, _, _, _, H₁, H₂⟩
      exact ⟨fun l => (H₁ l.1 l.2).1, fun l => (H₁ l.1 l.2).2.1, fun l => (H₁ l.1 l.2).2.2, H₂⟩
    · rintro ⟨H₁, H₂, H₃, H₄⟩
      exact ⟨g _, g _, g _, g1, fun l hl => ⟨H₁ ⟨l, hl⟩, H₂ ⟨l, hl⟩, H₃ ⟨l, hl⟩⟩, H₄⟩
  let m' : Over.mk (m ≫ X.hom) ⟶ X := Over.homMk m rfl
  refine ⟨Over.mk (m ≫ X.hom), m' ≫ p₁ ≫ inc, m' ≫ p₂ ≫ inc, m' ≫ p₃ ≫ inc,
    inferInstanceAs (LocallyOfFiniteType (m ≫ X.hom)), inferInstanceAs (QuasiCompact (m ≫ X.hom)),
    (key _ m').2 ⟨fun l => hZ (.inl l), fun l => hZ (.inr (.inl l)), fun l => hZ (.inr (.inr (.inl l))),
      fun l => hZ (.inr (.inr (.inr l)))⟩, fun Y l₁ l₂ l₃ hl => ?_⟩
  have lf : ∀ l : Y ⟶ H, ⊤ ≤ l.left ⁻¹ᵁ C.W a → ∃ q : Y ⟶ W, q ≫ inc = l := by
    intro l h
    have hr : Set.range l.left ⊆ Set.range (C.W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact h trivial
    refine ⟨Over.homMk (IsOpenImmersion.lift (C.W a).ι l.left hr) ?_, ?_⟩
    · change _ ≫ (C.W a).ι ≫ H.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w]
    · ext1
      exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨q₁, rfl⟩ := lf l₁ hl.1
  obtain ⟨q₂, rfl⟩ := lf l₂ hl.2.1
  obtain ⟨q₃, rfl⟩ := lf l₃ hl.2.2.1
  let f : Y ⟶ X := lift q₁ (lift q₂ q₃)
  have f₁ : f ≫ p₁ ≫ inc = q₁ ≫ inc := by simp [f, p₁]
  have f₂ : f ≫ p₂ ≫ inc = q₂ ≫ inc := by simp [f, p₂]
  have f₃ : f ≫ p₃ ≫ inc = q₃ ≫ inc := by simp [f, p₃]
  rw [← f₁, ← f₂, ← f₃] at hl ⊢
  obtain ⟨H₁, H₂, H₃, H₄⟩ := (key Y f).1 hl
  obtain ⟨z, hz⟩ := hu Y.left f.left (by
    rintro (l | l | l | l)
    exacts [H₁ l, H₂ l, H₃ l, H₄ l])
  let z' : Y ⟶ Over.mk (m ≫ X.hom) := Over.homMk z (by
    change z ≫ m ≫ X.hom = _
    rw [← Category.assoc, hz, Over.w])
  have hz' : z' ≫ m' = f := Over.OverMorphism.ext hz
  exact ⟨z', by rw [← Category.assoc z', hz'], by rw [← Category.assoc z', hz'], by rw [← Category.assoc z', hz']⟩

theorem appTop_charUnit_mul {X : Type} [AddCommGroup X] {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S X) (χ : X) :
    (t₁ * t₂).left.appTop.hom (charUnit S X χ).val =
      t₁.left.appTop.hom (charUnit S X χ).val * t₂.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    ← splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem torus_ext {d : ℕ} {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S (Fin d → ℤ))
    (h : ∀ n, t₁.left.appTop.hom (charUnit S _ (Pi.single n 1)).val =
      t₂.left.appTop.hom (charUnit S _ (Pi.single n 1)).val) : t₁ = t₂ := by
  apply (splitTorusPointsEquiv S _ Y).injective
  apply MonoidHom.toAdditiveRight.injective
  refine AddMonoidHom.toIntLinearMap_injective ((Pi.basisFun ℤ (Fin d)).ext fun n => ?_)
  rw [Pi.basisFun_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  exact (splitTorusPointsEquiv_val S _ Y t₁ _).trans ((h n).trans (splitTorusPointsEquiv_val S _ Y t₂ _).symm)

theorem rel_of_kerIs {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I}
    {i : splitTorus S (Fin d → ℤ) ⟶ H} (hi : C.KerIs a j i) {Y : Over S} (t₁ t₂ : Y ⟶ splitTorus S (Fin d → ℤ)) :
    Rel C a j (t₁ ≫ i).left (t₂ ≫ i).left ((t₁ * t₂) ≫ i).left (1 : Y ⟶ H).left := by
  obtain ⟨h₁, h, H₁⟩ := (hi.2.1 Y _).2 ⟨t₁, rfl⟩
  obtain ⟨h₂, _, H₂⟩ := (hi.2.1 Y _).2 ⟨t₂, rfl⟩
  obtain ⟨h₃, _, H₃⟩ := (hi.2.1 Y _).2 ⟨t₁ * t₂, rfl⟩
  refine ⟨h₁, h₂, h₃, h, fun l hl => ⟨H₁ l hl, H₂ l hl, H₃ l hl⟩, fun n => ?_⟩
  rw [hi.2.2 Y t₁ n h₁ h, hi.2.2 Y t₂ n h₂ h, hi.2.2 Y _ n h₃ h, appTop_charUnit_mul]
  ring

theorem mul_eq_of_rel {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {c : Fin d → C.Cl} {j : Fin d → C.I}
    {i : splitTorus S (Fin d → ℤ) ⟶ H} [IsMonHom i] (hi : C.KerIs a j i) (hb : C.Based c a j) {Y : Over S}
    {k₁ k₂ k₃ : Y ⟶ H} (hk : Rel C a j k₁.left k₂.left k₃.left (1 : Y ⟶ H).left) : k₁ * k₂ = k₃ := by
  obtain ⟨h₁, h₂, h₃, h, H₁, H₂⟩ := hk
  obtain ⟨t₁, rfl⟩ := (hi.2.1 Y k₁).1 ⟨h₁, h, fun l hl => (H₁ l hl).1⟩
  obtain ⟨t₂, rfl⟩ := (hi.2.1 Y k₂).1 ⟨h₂, h, fun l hl => (H₁ l hl).2.1⟩
  obtain ⟨t₃, rfl⟩ := (hi.2.1 Y k₃).1 ⟨h₃, h, fun l hl => (H₁ l hl).2.2⟩
  rw [← MonObj.mul_comp]
  congr 1
  refine torus_ext _ _ fun n => ?_
  have e := H₂ n
  rw [hi.2.2 Y t₁ n h₁ h, hi.2.2 Y t₂ n h₂ h, hi.2.2 Y _ n h₃ h] at e
  have hu : IsUnit (((1 : Y ⟶ H).left.appLE _ ⊤ h).hom (C.r a (j n))) := by
    refine RingedSpace.isUnit_of_isUnit_germ (X := Y.left.toRingedSpace) ⊤ _ fun x hx => ?_
    refine (Scheme.mem_basicOpen Y.left _ x hx).1 ?_
    erw [Scheme.basicOpen_appLE]
    exact ⟨trivial, (toUnit Y).left.preimage_mono (hb.2 n).2 trivial⟩
  rw [appTop_charUnit_mul]
  refine (hu.mul hu).mul_right_cancel ?_
  linear_combination e

theorem eSec_pull {S' : Scheme.{0}} (t : S' ⟶ S) :
    ∃ q, eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t = q ≫ eSec H := by
  refine ⟨(Functor.LaxMonoidal.ε (Over.pullback t)).left ≫ pullback.fst _ t, ?_⟩
  rw [Category.assoc]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (SplitTorusPoints.map_left_fst t η[H]))

theorem based_pull {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {c : Fin d → C.Cl} {j : Fin d → C.I}
    (hb : C.Based c a j) :
    Charts.Based (H := (Over.pullback t).obj H) (C.pull (pullback.fst H.hom t)) c a j := by
  obtain ⟨q, hq⟩ := eSec_pull (H := H) t
  refine ⟨?_, fun n => ⟨(hb.2 n).1, ?_⟩⟩
  · change ⊤ ≤ (eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t) ⁻¹ᵁ C.W a
    rw [hq]
    exact q.preimage_mono hb.1
  · have e := Scheme.preimage_basicOpen (pullback.fst H.hom t) (C.r a (j n))
    have : ⊤ ≤ (eSec ((Over.pullback t).obj H) ≫ pullback.fst H.hom t) ⁻¹ᵁ H.left.basicOpen (C.r a (j n)) := by
      rw [hq]
      exact q.preimage_mono (hb.2 n).2
    rw [Scheme.Hom.comp_preimage, e] at this
    exact this

theorem one_left_fst {S' : Scheme.{0}} (t : S' ⟶ S) (Y' : Over S') (Y : Over S) (p : Y'.left ⟶ Y.left)
    (hp : p ≫ Y.hom = Y'.hom ≫ t) :
    (1 : Y' ⟶ (Over.pullback t).obj H).left ≫ pullback.fst H.hom t = p ≫ (1 : Y ⟶ H).left := by
  let z : Y' ⟶ (Over.pullback t).obj Y := Over.homMk (pullback.lift p Y'.hom hp) (pullback.lift_snd _ _ _)
  rw [← MonObj.comp_one z, ← Functor.map_one, Over.comp_left, Category.assoc, SplitTorusPoints.map_left_fst,
    ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

theorem rel_map {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I} {Z : Over S} {k₁ k₂ k₃ : Z ⟶ H}
    (hk : Rel C a j k₁.left k₂.left k₃.left (1 : Z ⟶ H).left) :
    Rel (C.pull (pullback.fst H.hom t)) a j ((Over.pullback t).map k₁).left ((Over.pullback t).map k₂).left
      ((Over.pullback t).map k₃).left (1 : (Over.pullback t).obj Z ⟶ (Over.pullback t).obj H).left := by
  refine (rel_pull C _ a j _ _ _ _).2 ?_
  have e := one_left_fst (H := H) t ((Over.pullback t).obj Z) Z (pullback.fst _ _) pullback.condition
  have h := hk.comp (pullback.fst Z.hom t)
  rw [← SplitTorusPoints.map_left_fst, ← SplitTorusPoints.map_left_fst, ← SplitTorusPoints.map_left_fst] at h
  exact e ▸ h

theorem mul_eq_of_univ {S' : Scheme.{0}} (t : S' ⟶ S) [IsAffineHom (pullback.fst H.hom t)]
    {C : Charts H.left} {a : {i // C.wt i = C.c₀}} {d : ℕ} {j : Fin d → C.I} {Z : Over S} {k₁ k₂ k₃ : Z ⟶ H}
    (hu : ∀ (Y : Over S) (l₁ l₂ l₃ : Y ⟶ H), Rel C a j l₁.left l₂.left l₃.left (1 : Y ⟶ H).left →
        ∃ z : Y ⟶ Z, z ≫ k₁ = l₁ ∧ z ≫ k₂ = l₂ ∧ z ≫ k₃ = l₃)
    (hgen : (Over.pullback t).map (k₁ * k₂) = (Over.pullback t).map k₃) {Y : Over S'}
    {l₁ l₂ l₃ : Y ⟶ (Over.pullback t).obj H}
    (hl : Rel (C.pull (pullback.fst H.hom t)) a j l₁.left l₂.left l₃.left
      (1 : Y ⟶ (Over.pullback t).obj H).left) : l₁ * l₂ = l₃ := by
  have h := (rel_pull C _ a j _ _ _ _).1 hl
  let Y₀ : Over S := Over.mk (Y.hom ≫ t)
  let P (k : Y ⟶ (Over.pullback t).obj H) : Y₀ ⟶ H :=
    Over.homMk (k.left ≫ pullback.fst H.hom t) (by
      change _ = Y.hom ≫ t
      rw [← Over.w k]
      exact (Category.assoc _ _ _).trans ((congrArg (k.left ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm))
  have e := (one_left_fst (H := H) t Y Y₀ (𝟙 _) (Category.id_comp _)).trans (Category.id_comp _)
  obtain ⟨z, h₁, h₂, h₃⟩ := hu Y₀ (P l₁) (P l₂) (P l₃) (e ▸ h)
  let z' : Y ⟶ (Over.pullback t).obj Z :=
    Over.homMk (pullback.lift z.left Y.hom (Over.w z)) (pullback.lift_snd _ _ _)
  have key : ∀ (k : Z ⟶ H) (l : Y ⟶ (Over.pullback t).obj H), z ≫ k = P l →
      z' ≫ (Over.pullback t).map k = l := by
    intro k l hl
    ext1
    refine pullback.hom_ext ?_ ((Over.w _).trans (Over.w l).symm)
    refine (Category.assoc _ _ _).trans ((congrArg (z'.left ≫ ·) (SplitTorusPoints.map_left_fst t k)).trans
      ((Category.assoc _ _ _).symm.trans ?_))
    exact (congrArg (· ≫ k.left) (pullback.lift_fst _ _ _)).trans (congrArg CommaMorphism.left hl)
  rw [← key _ _ h₃, ← hgen, Functor.map_mul, MonObj.comp_mul, key _ _ h₁, key _ _ h₂]

theorem isMonHom_of_mul {T : Over S} [GrpObj T] (i : T ⟶ H)
    (hmul : ∀ (Y : Over S) (t₁ t₂ : Y ⟶ T), (t₁ ≫ i) * (t₂ ≫ i) = (t₁ * t₂) ≫ i) : IsMonHom i := by
  constructor
  · have h := hmul (𝟙_ _) 1 1
    rw [_root_.mul_one, mul_eq_left, Hom.one_def, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _)] at h
    simpa using h
  · have h := hmul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← h]
    congr 1

theorem isMonHom_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → IsMonHom i := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hb i hi
  obtain ⟨Z, k₁, k₂, k₃, _, _, hk, hu⟩ := exists_rep C a j hb.1
  have hgen := GenericEq.map_eq_generic R Z Sg hD G (k₁ * k₂) k₃ fun x hx => by
    obtain ⟨K, _, t, _, ht, hc, i', hT⟩ := hS x hx
    refine ⟨K, inferInstance, t, ht, ?_⟩
    have := hT.hom
    have : Smooth ((Over.pullback t).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom t))
    have : IsSeparated ((Over.pullback t).obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom t))
    have : QuasiCompact ((Over.pullback t).obj G).hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
    have hb' := based_pull t hb
    rw [Functor.map_mul]
    exact mul_eq_of_rel (GlobalTheory.T.torus_cut_by_invariantRatios_field K ((Over.pullback t).obj G) _ d c i' a j hc hT hb') hb' (rel_map t hk)
  exact isMonHom_of_mul i fun Y t₁ t₂ => mul_eq_of_univ (Out.jK R) hu hgen (rel_of_kerIs hi t₁ t₂)

end GlobalTheory.ZJ.KerSubgroup
end
