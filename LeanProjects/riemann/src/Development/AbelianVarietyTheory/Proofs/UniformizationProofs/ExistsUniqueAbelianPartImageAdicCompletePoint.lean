import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.PointImage

def levelHom {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ n →+* W ⧸ (I.map f) ^ n :=
  Ideal.quotientMap _ f (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)

theorem isPushout_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (n : ℕ) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n))) (CommRingCat.ofHom (levelHom f I n)) := by
  have w : CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I.map f) ^ n)) =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)) ≫ CommRingCat.ofHom (levelHom f I n) := rfl
  have hk : ∀ s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))),
      ∀ a ∈ (I.map f) ^ n, s.inl.hom a = 0 := by
    intro s a ha
    rw [← Ideal.map_pow] at ha
    have : (I ^ n).map f ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have h := congrArg (fun φ => φ.hom y) s.condition
      change s.inl.hom (f y) = s.inr.hom (Ideal.Quotient.mk _ y) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero] at h
      exact h
    exact this ha
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (hk s))) (fun s => rfl)
    (fun s => ?_) (fun s m h _ => ?_)⟩⟩
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom s.condition
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom h

theorem isPullback_level {R W : Type} [CommRing R] [CommRing W] (f : R →+* W) (I : Ideal R) (e : ℕ) :
    IsPullback (adicLevelι (I.map f) (e + 1)) (Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))))
      (Spec.map (CommRingCat.ofHom f)) (thick R I e) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_level f I (e + 1))

theorem thick_mono' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem existsUnique_image {R W : Type} [CommRing R] [CommRing W] [IsLocalRing W] (f : R →+* W)
    (I : Ideal R) [IsAdicComplete (I.map f) W] {G B : Scheme.{0}}
    (pG : G ⟶ Spec (CommRingCat.of R)) (pB : B ⟶ Spec (CommRingCat.of R))
    {P : ℕ → Scheme.{0}} (fst : ∀ e, P e ⟶ G)
    (snd : ∀ e, P e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hP : ∀ e, IsPullback (fst e) (snd e) pG (thick R I e))
    (τ : ∀ e, P e ⟶ P (e + 1)) (hm : ∀ e, τ e ≫ fst (e + 1) = fst e)
    (φ : ∀ e, P e ⟶ B) (hφ : ∀ e, φ e ≫ pB = snd e ≫ thick R I e)
    (hc : ∀ e, τ e ≫ φ (e + 1) = φ e)
    (x : Spec (CommRingCat.of W) ⟶ G) (hx : x ≫ pG = Spec.map (CommRingCat.ofHom f)) :
    ∃! b : Spec (CommRingCat.of W) ⟶ B, b ≫ pB = Spec.map (CommRingCat.ofHom f) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ P e),
        xe ≫ fst e = r ≫ x → xe ≫ φ e = r ≫ b := by
  have hw : ∀ e, (adicLevelι (I.map f) (e + 1) ≫ x) ≫ pG =
      Spec.map (CommRingCat.ofHom (levelHom f I (e + 1))) ≫ thick R I e := fun e => by
    rw [← (isPullback_level f I e).w, Category.assoc, hx]
  choose y hy hy2 using fun e => (hP e).exists_lift _ _ (hw e)
  have hmono : ∀ e, Mono (fst e) := fun e =>
    (MorphismProperty.monomorphisms Scheme).of_isPullback (hP e).flip (thick_mono' R I e)
  have hfam : IsAdicFamily (I.map f) (fun e => y e ≫ φ e) := by
    intro e
    have : adicLevelMap (I.map f) (Nat.le_succ (e + 1)) ≫ y (e + 1) = y e ≫ τ e := by
      rw [← cancel_mono (fst (e + 1)), Category.assoc, hy,
        adicLevelMap_ι_assoc, Category.assoc, hm, hy]
    change _ ≫ y (e + 1) ≫ φ (e + 1) = y e ≫ φ e
    rw [← hc e, ← Category.assoc, this, Category.assoc]
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom f))
    pB hfam (fun e => by
      rw [(isPullback_level f I e).w, ← hy2, Category.assoc, hφ, Category.assoc])
  refine ⟨g, ⟨hg, fun e Z r xe h => ?_⟩, fun b hb => ?_⟩
  · have hr : r ≫ Spec.map (CommRingCat.ofHom f) = (xe ≫ snd e) ≫ thick R I e := by
      rw [← hx, ← Category.assoc, ← h, Category.assoc, (hP e).w, Category.assoc]
    obtain ⟨l, hl, -⟩ := (isPullback_level f I e).exists_lift _ _ hr
    have hxe : xe = l ≫ y e := by
      rw [← cancel_mono (fst e), h, ← hl, Category.assoc, Category.assoc, hy]
    rw [hxe, ← hl, Category.assoc, Category.assoc, hg']
  · exact hu b ⟨hb.1, fun e => (hb.2 e _ _ (y e) (hy e)).symm⟩

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, ∃! b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  obtain ⟨g, ⟨hg, hg'⟩, hu⟩ := existsUnique_image (algebraMap V W) (IsLocalRing.maximalIdeal V)
    G.hom a.B.hom (P := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).left)
    (fun e => (fstG _ e G).left) (fun e => (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)
    (fun e => IsPullback.of_hasPullback G.hom (thick V _ e)) (fun e => thickMap V _ e G)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _))
    (fun e => (t.l e).Q.q.left ≫ a.b e)
    (fun e => by
      obtain ⟨h, -⟩ := a.b_pb e
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← a.b_β e, ← Category.assoc, ← t.β_q e, Category.assoc])
    x.left (Over.w x)
  exact ⟨Over.homMk g hg, hg', fun b hb => Over.OverMorphism.ext (hu b.left ⟨Over.w b, hb⟩)⟩

end GlobalTheory.UU.PointImage
end
