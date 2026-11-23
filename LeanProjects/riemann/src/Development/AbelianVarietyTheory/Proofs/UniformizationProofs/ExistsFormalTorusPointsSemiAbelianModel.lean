import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.FormalTorusPts

theorem scal_comp {W : Type} [CommRing W] {Z Z' : Scheme.{0}} (h : Z' ⟶ Z)
    (r : Z ⟶ Spec (CommRingCat.of W)) (w : W) : scal (h ≫ r) w = h.appTop.hom (scal r w) := by
  rw [scal, scal, Scheme.Hom.comp_appTop]; rfl

theorem scal_specMap {W W' : Type} [CommRing W] [CommRing W'] {Z : Scheme.{0}} (φ : W →+* W')
    (r : Z ⟶ Spec (CommRingCat.of W')) (w : W) :
    scal (r ≫ Spec.map (CommRingCat.ofHom φ)) w = scal r (φ w) :=
  congr($(SplitTorusPoints.ΓSpecIso_inv_comp_specMap r (CommRingCat.ofHom φ)).hom w)

theorem exists_lift_quot {W : Type} [CommRing W] (J : Ideal W) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (h : ∀ w ∈ J, scal r w = 0) :
    ∃ r' : Z ⟶ Spec (CommRingCat.of (W ⧸ J)),
      r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  let φ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J φ.hom h)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp]
  change Z.toSpecΓ ≫ Spec.map φ = r
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of W)).inv,
    SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
    Category.comp_id]

variable {R : Type} [CommRing R] (I : Ideal R) (W : Type) [CommRing W] [Algebra R W]

theorem pow_le_comap (n : ℕ) : I ^ n ≤ ((I.map (algebraMap R W)) ^ n).comap (algebraMap R W) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]

def lev (e : ℕ) : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶
    Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R W) (pow_le_comap I W (e + 1))))

theorem lev_thick (e : ℕ) : lev I W e ≫ thick R I e =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]; rfl

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have := isClosedImmersion_red (I ^ (e + 1))
  infer_instance

variable {X : Type} [AddCommGroup X] {W}

def pt (e : ℕ) (a : Multiplicative X →* Wˣ) :
    Over.mk (lev I W e) ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X :=
  (splitTorusPointsEquiv _ X (Over.mk (lev I W e))).symm
    ((Units.map ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (adicLevelι (I.map (algebraMap R W)) (e + 1)).appTop).hom.toMonoidHom).comp a)

theorem pt_mul (e : ℕ) (a b : Multiplicative X →* Wˣ) : pt I e (a * b) = pt I e a * pt I e b := by
  rw [pt, pt, pt, ← map_mul]
  congr 1
  ext χ
  simp

theorem pt_char (e : ℕ) (a : Multiplicative X →* Wˣ) (χ : X) :
    (pt I e a).left.appTop.hom (charUnit _ X χ).val =
      scal (adicLevelι (I.map (algebraMap R W)) (e + 1)) (a (Multiplicative.ofAdd χ)).val := by
  rw [← splitTorusPointsEquiv_val, pt, MulEquiv.apply_symm_apply]
  rfl

theorem pt_hom (e : ℕ) (a : Multiplicative X →* Wˣ) :
    (pt I e a).left ≫ (splitTorus _ X).hom = lev I W e := Over.w (pt I e a)

theorem exists_factor (e : ℕ) (a : Multiplicative X →* Wˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left)
    (h : τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)))
    (hχ : ∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) :
    ∃ r', r' ≫ adicLevelι (I.map (algebraMap R W)) (e + 1) = r ∧ r' ≫ (pt I e a).left = τ := by
  have hk : ∀ w ∈ (I.map (algebraMap R W)) ^ (e + 1), scal r w = 0 := by
    have : (I.map (algebraMap R W)) ^ (e + 1) ≤ RingHom.ker
        ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop).hom := by
      rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro v hv
      change scal r (algebraMap R W v) = 0
      rw [← scal_specMap, ← h, ← Category.assoc, scal_specMap, Ideal.Quotient.eq_zero_iff_mem.2 hv]
      simp [scal]
    exact fun w hw => this hw
  obtain ⟨r', hr⟩ := exists_lift_quot _ r hk
  refine ⟨r', hr, splitTorus_left_hom_ext _ _ ?_ fun χ => ?_⟩
  · rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc, h,
      ← Category.assoc (pt I e a).left, pt_hom, lev_thick, ← hr]
    exact (Category.assoc _ _ _).symm
  · rw [hχ, ← hr, scal_comp, ← pt_char, Scheme.Hom.comp_appTop]
    rfl

variable {G : Over (Spec (CommRingCat.of R))}
  (i : ∀ e, splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X ⟶ thickObj R I e G)

def gpt (a : Multiplicative X →* Wˣ) (e : ℕ) :
    Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶ G.left :=
  (pt I e a).left ≫ (i e).left ≫ pullback.fst G.hom (thick R I e)

theorem gpt_hom (a : Multiplicative X →* Wˣ) (e : ℕ) : gpt I i a e ≫ G.hom =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [← lev_thick, ← pt_hom I e a, ← Over.w (i e), gpt]
  simp only [Category.assoc]
  congr 2
  exact pullback.condition

theorem isAdicFamily_aux
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (a : Multiplicative X →* Wˣ) : IsAdicFamily (I.map (algebraMap R W)) (gpt I i a) := by
  intro e
  obtain ⟨τ, h1, h2, h3⟩ := hi e
  have h4 : adicLevelMap (I.map (algebraMap R W)) (Nat.le_succ (e + 1)) ≫ (pt I (e + 1) a).left =
      (pt I e a).left ≫ τ := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [← cancel_mono (thick R I (e + 1))]
      simp only [Category.assoc]
      rw [← Category.assoc (pt I (e + 1) a).left, pt_hom, lev_thick, adicLevelMap_ι_assoc,
        ← Category.assoc τ, h1, Category.assoc, thickTrans_comp, ← Category.assoc, pt_hom, lev_thick]
    · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp,
        RingHom.comp_apply, RingHom.comp_apply, h2, pt_char, pt_char, ← scal_comp, adicLevelMap_ι]
  have h5 : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) =
      pullback.fst G.hom (thick R I e) := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [gpt, gpt, ← Category.assoc, h4, Category.assoc, ← Category.assoc τ, h3, Category.assoc, h5]

theorem exists_hom [GrpObj G] [IsLocalRing W] [IsAdicComplete (I.map (algebraMap R W)) W]
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (hm : ∀ e, IsMonHom (i e)) (hmono : ∀ e, Mono (i e)) :
    ∃ ι' : (Multiplicative X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G),
      Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G)
        (a : Multiplicative X →* Wˣ), x = ι' a ↔
        ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left),
          τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
            r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) →
          (∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) →
          τ ≫ (i e).left ≫ pullback.fst G.hom (thick R I e) = r ≫ x.left := by
  have ex := fun a : Multiplicative X →* Wˣ =>
    (existsUnique_over_of_isAdicFamily _ G.hom (isAdicFamily_aux I i hi a) (gpt_hom I i a)).exists
  choose g hg hg' using ex
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W)))
  let f : (Multiplicative X →* Wˣ) → (T ⟶ G) := fun a => Over.homMk (g a) (hg a)
  have hf : ∀ a e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ (f a).left = gpt I i a e := hg'
  have hext : ∀ (x : T ⟶ G) a,
      (∀ e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ x.left = gpt I i a e) → x = f a :=
    fun x a h => Over.OverMorphism.ext
      (hom_ext_of_isHausdorff (I.map (algebraMap R W)) fun e => (h e).trans (hf a e).symm)
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    refine (hext _ _ fun e => ?_).symm
    have := hm e
    let k : Over.mk ((Over.mk (lev I W e)).hom ≫ thick R I e) ⟶ T :=
      Over.homMk (adicLevelι (I.map (algebraMap R W)) (e + 1)) (lev_thick I W e).symm
    have hk : ∀ c, (k ≫ f c).left = (pt I e c ≫ i e).left ≫ pullback.fst G.hom (thick R I e) :=
      fun c => (hf c e).trans (Category.assoc _ _ _).symm
    have h := SplitTorus.mul_left_comp_fst G (thick R I e) (pt I e a ≫ i e) (pt I e b ≫ i e)
      (k ≫ f a) (k ≫ f b) (hk a) (hk b)
    rw [← MonObj.comp_mul, ← MonObj.mul_comp, ← pt_mul] at h
    exact h.trans (Category.assoc _ _ _)
  refine ⟨MonoidHom.mk' f hmul, fun a b hab => ?_, fun x a => ⟨?_, fun h => hext x a fun e => ?_⟩⟩
  · refine MonoidHom.ext fun χ => Units.ext ?_
    refine IsHausdorff.StrictMono.funext' (I.map (algebraMap R W)) (a := fun n => n + 1)
      (strictMono_id.add_const 1) (f := fun _ : Unit => (a χ).val) (g := fun _ => (b χ).val)
      (fun e _ => ?_) |> (congrFun · ())
    have := hmono e
    have : Mono (i e).left := inferInstanceAs (Mono ((Over.forget _).map (i e)))
    have h1 : gpt I i a e = gpt I i b e := by
      rw [← hf, ← hf]; exact congrArg (fun y : T ⟶ G => _ ≫ y.left) hab
    rw [gpt, gpt, cancel_mono] at h1
    have h2 := pt_char I e a χ.toAdd
    rw [h1, pt_char, ← Category.id_comp (adicLevelι _ _), scal_specMap, scal_specMap] at h2
    simp only [scal, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1 h2).symm
  · rintro rfl e Z r τ h hχ
    obtain ⟨r', rfl, rfl⟩ := exists_factor I e a r τ h hχ
    rw [Category.assoc, Category.assoc]
    exact congrArg (r' ≫ ·) (hf a e).symm
  · refine (h e _ _ (pt I e a).left ?_ (pt_char I e a)).symm
    rw [← Category.assoc, pt_hom, lev_thick]

end GlobalTheory.UU.FormalTorusPts

namespace GlobalTheory.UU

theorem exists_formalTorus_points :
    AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  intro V _ _ _ A G _ _ s t W _ _ _ hW _
  refine FormalTorusPts.exists_hom (IsLocalRing.maximalIdeal V) (fun e => (t.l e).Q.i) t.tor
    (fun e => (t.l e).Q.i_hom) fun e => ?_
  exact ⟨fun a b h => (t.l e).Q.isKernel.hom_ext h (toUnit_unique _ _)⟩

end GlobalTheory.UU
end
