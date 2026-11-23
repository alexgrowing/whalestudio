import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TrivProdOfSmallExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen

noncomputable section

namespace GlobalTheory.Exist.ProdOpen

section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)

def prodMap : ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left ≫ pullback.fst (X ⊗ Y).hom φ

theorem isPullback_prodMap :
    IsPullback (prodMap φ X Y) ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
      (X ⊗ Y).hom φ := by
  have h := IsPullback.of_hasPullback (X ⊗ Y).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  rw [← hw]
  exact isPullback_iso_comp h _

theorem lift_prodMap {Z : Over S} (a : Z ⟶ X) (b : Z ⟶ Y) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ prodMap φ X Y =
      pullback.fst Z.hom φ ≫ (lift a b).left := by
  rw [prodMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _

theorem toUnit_section (y : 𝟙_ (Over S) ⟶ Y) :
    toUnit ((Over.pullback φ).obj X) ≫ Functor.LaxMonoidal.ε (Over.pullback φ) ≫
      (Over.pullback φ).map y = (Over.pullback φ).map (toUnit X ≫ y) := by
  rw [← Category.assoc, Functor.Monoidal.toUnit_ε, Functor.map_comp]

end BaseChange

theorem bijective_baseChange {R T : Type} [CommRing R] [CommRing T] (g₁ : R →+* T) (X : Over (Sp R))
    (h : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom)) :
    (∀ (R' : Type) [CommRing R'] (g : T →+* R') (X' : Scheme.{0}) (π : X' ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by
  intro R' _ g X' π f' hp
  have hq := hp.paste_horiz (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom g₁)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
  exact h R' _ X' _ f' hq

theorem triv_lift_prod {R : Type} [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X)
    (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y) [Flat X.hom] [Flat Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hX : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (hY : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (M : LB (X ⊗ Y).left) (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left))
    (h₂ : Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (X ⊗ Y).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫
          Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π)) :
    Triv (M.pull (prodMap (Spec.map (CommRingCat.ofHom g)) X Y)) := by
  let φ : Sp T ⟶ Sp R := Spec.map (CommRingCat.ofHom g)
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine GlobalTheory.SmallExtLift.triv_prod_of_small_extension T e he ((Over.pullback φ).obj X) ((Over.pullback φ).obj Y)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map x₀)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map y₀)
    (inferInstanceAs (Flat (pullback.snd X.hom φ))) (inferInstanceAs (Flat (pullback.snd Y.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd X.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd Y.hom φ)))
    (bijective_baseChange g X hX) (bijective_baseChange g Y hY) (M.pull (prodMap φ X Y))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst X.hom φ) ?_ h₁)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst Y.hom φ) ?_ h₂)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_prodMap φ X Y)))

theorem surjective_prod {S : Scheme.{0}} (X Y : Over S) (x₀ : 𝟙_ (Over S) ⟶ X)
    (y₀ : 𝟙_ (Over S) ⟶ Y) : Surjective (X ⊗ Y).hom := by
  have hw : (lift x₀ y₀).left ≫ (X ⊗ Y).hom = 𝟙 S := Over.w (lift x₀ y₀)
  refine ⟨fun s => ⟨(lift x₀ y₀).left s, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, hw]
  rfl

theorem triv_basicOpen_of_triv_fibre_prod : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro R _ X Y x₀ y₀ _ _ _ _ hX hY hXY M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  haveI : IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ (X ⊗ Y).hom M hM hP inferInstance
    (surjective_prod X Y x₀ y₀) K g₀ X₀ π₀ f₀ h₀ (hXY K g₀ X₀ π₀ f₀ h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_prodMap (Spec.map (CommRingCat.ofHom g)) X Y) (hu r hr)).1 ?_
      refine triv_lift_prod X Y x₀ y₀ hX hY M hM h₁ h₂ T g e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (X ⊗ Y).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht

end GlobalTheory.Exist.ProdOpen
