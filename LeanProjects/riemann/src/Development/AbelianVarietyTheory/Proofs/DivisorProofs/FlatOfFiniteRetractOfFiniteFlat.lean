import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem retract_flat_of_finite (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H)
    (hsr : s ≫ r = 𝟙 H) (hH : IsFinite H.hom) (hK : IsFinite K.hom) (hKf : Flat K.hom) :
    Flat H.hom := by
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  haveI : IsAffine K.left := isAffine_of_isAffineHom K.hom
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)] at hKf ⊢
  have wr : r.left ≫ H.hom = K.hom := Over.w r
  have ws : s.left ≫ K.hom = H.hom := Over.w s
  have hid : s.left ≫ r.left = 𝟙 H.left := by rw [← Over.comp_left, hsr, Over.id_left]
  letI := H.hom.appTop.hom.toAlgebra
  letI := K.hom.appTop.hom.toAlgebra
  have hKf' : Module.Flat Γ(Sp R, ⊤) Γ(K.left, ⊤) := hKf
  show Module.Flat Γ(Sp R, ⊤) Γ(H.left, ⊤)
  let rs : Γ(H.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(K.left, ⊤) :=
    { toFun := r.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (H.hom.appTop ≫ r.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, wr]; rfl }
  let ss : Γ(K.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(H.left, ⊤) :=
    { toFun := s.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (K.hom.appTop ≫ s.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, ws]; rfl }
  refine Module.Flat.of_retract rs ss ?_
  ext x
  show (r.left.appTop ≫ s.left.appTop) x = x
  rw [← Scheme.Hom.comp_appTop, hid]
  simp

end GlobalTheory
