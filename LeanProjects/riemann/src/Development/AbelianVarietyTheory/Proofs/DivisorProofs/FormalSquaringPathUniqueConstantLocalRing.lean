import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegreesStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem comp_grpMul {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (x : T' ⟶ T) (f g : T ⟶ G) :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, Subsingleton.elim (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  have : (η[G] : 𝟙_ (Over S) ⟶ G) ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [comp_grpMul, Category.comp_id, h1, _root_.one_mul]
  exact congrArg (·.left) this

theorem triv_isPath {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (c : R) (b : Sp R ⟶ S) :
    IsPath G c b (triv G b) where
  base := triv_over G b
  zero := by
    rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.constantCoeff (R := R))) = 𝟙 _ := by
      ext x; simp
    rw [this, Spec.map_id, Category.id_comp]
  scale := by
    rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.rescale c)) = CommRingCat.ofHom (PowerSeries.C (R := R)) := by
      ext x n; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with h <;> simp [h]
    rw [this, Category.assoc, Category.assoc, unitSec_comp_sqr]

theorem eq_unitSec_of_sqr_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (z : Sp R ⟶ G.left)
    (hz : z ≫ sqr G = z) : z = (z ≫ G.hom) ≫ unitSec G := by
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h : z' * z' = z' := by
    have e := comp_grpMul z' (𝟙 G) (𝟙 G)
    rw [Category.comp_id] at e
    rw [← e]
    ext
    exact hz
  have h1 : z' = 1 := by simpa using h
  have h2 := congrArg (·.left) h1
  rw [Hom.one_def] at h2
  refine h2.trans ?_
  rw [Over.comp_left]
  congr 1

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem triv_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  intro S G _ R _
  refine ⟨fun c b => triv_isPath G c b, fun z hz => eq_unitSec_of_sqr_eq G z hz, ?_⟩
  intro _ hq c hc b ξ hξ
  exact GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees S G R hq c 1 one_pos hc b ξ (triv G b) hξ (triv_isPath G c b)
    (fun _ _ _ _ j hj hj' => absurd hj' (by omega))

end GlobalTheory.Nef
