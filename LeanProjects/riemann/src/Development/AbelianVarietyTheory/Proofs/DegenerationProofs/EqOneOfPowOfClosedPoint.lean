import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.RedPts

variable {S : Scheme.{0}}

def precomp (G : Over S) [GrpObj G] {T T' : Over S} (u : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := u ≫ x
  map_one' := MonObj.comp_one u
  map_mul' x y := MonObj.comp_mul u x y

def diagSec {T : Scheme.{0}} (p : T ⟶ S) : 𝟙_ (Over T) ⟶ (Over.pullback p).obj (Over.mk p) :=
  Over.homMk (pullback.lift (𝟙 T) (𝟙 T) rfl) (pullback.lift_snd _ _ _)

def toSec (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    (Over.mk p ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback p).obj G) :=
  (precomp _ (diagSec p)).comp (Over.pullback p).homMonoidHom

theorem toSec_left_fst (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) (x : Over.mk p ⟶ G) :
    (toSec G p x).left ≫ pullback.fst G.hom p = x.left := by
  have h₁ : ((Over.pullback p).map x).left ≫ pullback.fst G.hom p = pullback.fst p p ≫ x.left :=
    pullback.lift_fst _ _ _
  have h₂ : (diagSec p).left ≫ pullback.fst p p = 𝟙 T := pullback.lift_fst _ _ _
  change ((diagSec p).left ≫ ((Over.pullback p).map x).left) ≫ _ = _
  rw [Category.assoc, h₁]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) h₂)).trans (Category.id_comp _)

theorem toSec_injective (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    Function.Injective (toSec G p) := fun x y h =>
  Over.OverMorphism.ext (by rw [← toSec_left_fst, h, toSec_left_fst])

theorem eq_one_of_pow_of_closedPoint (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by
  apply toSec_injective G p
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
  let G' := (Over.pullback p).obj G
  have : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  have := GlobalTheory.GrpTangent.formallyUnramified_mulN G' hn'
  have : LocallyOfFiniteType ((mulN G' n).left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G' n).left G'.hom
  refine Over.OverMorphism.ext (GlobalTheory.eq_of_isLocalRing_of_unramified (R := .of R) (mulN G' n).left
    (a := (toSec G p x).left) (b := (toSec G p 1).left) ?_ (show Z.left ⟶ Sp R from j.left) hj ?_)
  · have e : toSec G p x ≫ mulN G' n = toSec G p 1 ≫ mulN G' n := by
      rw [GlobalTheory.GrpTangent.comp_mulN, GlobalTheory.GrpTangent.comp_mulN, ← map_pow, ← map_pow, hx, one_pow]
    exact congrArg Over.Hom.left e
  · refine pullback.hom_ext ?_ ?_
    · have e : j ≫ x = j ≫ 1 := by rw [h, MonObj.comp_one]
      exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p x))).trans
        ((congrArg Over.Hom.left e).trans
          ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p 1))).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·)
        ((Over.w (toSec G p x)).trans (Over.w (toSec G p 1)).symm))).trans (Category.assoc _ _ _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_reduction : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ (H : Subgroup (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (r : H →* (𝟙_ (Over (Sp (IsLocalRing.ResidueField R))) ⟶ (Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G)), (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = x.left) ∧ (∀ (x : H) (s : Sp R ⟶ G.left), s ≫ G.hom = spMap (algebraMap W R) → spMap (algebraMap R Ω) ≫ s = x.1.left → (r x).left ≫ pullback.fst G.hom _ = spMap (IsLocalRing.residue R) ≫ s) ∧ ∀ (n : ℕ) (x : H), IsUnit (n : R) → x ^ n = 1 → r x = 1 → x = 1 := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hj G _ hG
  obtain ⟨hc, hsm, hsep, -, -⟩ := hG
  let u : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (algebraMap R Ω))
      ((spMap_comp _ _).trans (congrArg spMap (IsScalarTower.algebraMap_eq W R Ω).symm))
  let v : Over.mk (spMap ((IsLocalRing.residue R).comp (algebraMap W R))) ⟶
      Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (IsLocalRing.residue R)) (spMap_comp _ _)
  have hdom : IsDominant (spMap (algebraMap R Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hj]; exact bot_le)⟩
  have hu : Function.Injective (precomp G u) := fun a b h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp R) G.hom ((Over.w a).trans (Over.w b).symm)
      (spMap (algebraMap R Ω)) (congrArg Over.Hom.left h))
  let e := MonoidHom.ofInjective hu
  refine ⟨(precomp G u).range, ((toSec G _).comp (precomp G v)).comp e.symm.toMonoidHom,
    fun x => ⟨?_, ?_⟩, fun x s hs hx => ?_, fun n x hn hx hr => ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.left, Over.w s, rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨Over.homMk s hs, Over.OverMorphism.ext hx⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain rfl : y = Over.homMk s hs := hu (Over.OverMorphism.ext hx.symm)
    change (toSec G _ (precomp G v (e.symm (e _)))).left ≫ _ = _
    rw [e.symm_apply_apply, toSec_left_fst]
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective x
    change toSec G _ (precomp G v (e.symm (e _))) = _ at hr
    rw [e.symm_apply_apply, map_eq_one_iff _ (toSec_injective G _)] at hr
    rw [← map_pow, map_eq_one_iff _ e.injective] at hx
    rw [eq_one_of_pow_of_closedPoint G _ hn y hx v
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ hr, map_one]

end GlobalTheory.RedPts
