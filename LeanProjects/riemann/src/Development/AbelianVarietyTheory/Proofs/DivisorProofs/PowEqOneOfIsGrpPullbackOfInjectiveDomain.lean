import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pow_eq_one_of_isGrpPullback_of_injective : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  intro Ω T _ _ _ jT hj A P φ hφ x y k hxy hx
  let U : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have e1 : pushHom hφ (baseOver (Sp Ω)) x = U ≫ y := Over.OverMorphism.ext hxy
  have e2 : U ≫ y ^ k = U ≫ 1 :=
    calc U ≫ y ^ k = preHom U (y ^ k) := rfl
      _ = (preHom U y) ^ k := map_pow _ _ _
      _ = (pushHom hφ (baseOver (Sp Ω)) x) ^ k := by rw [e1]; rfl
      _ = pushHom hφ (baseOver (Sp Ω)) (x ^ k) := (map_pow _ _ _).symm
      _ = 1 := by rw [hx, map_one]
      _ = preHom U 1 := (map_one _).symm
  have e3 : spMap jT ≫ (y ^ k).left = spMap jT ≫ (1 : baseOver (Sp T) ⟶ P.A).left :=
    congrArg (fun z => z.left) e2
  have : IsDominant (spMap jT) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical jT).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot jT).1 hj]; exact bot_le)⟩
  have := P.isAb.proper
  have : IsReduced (baseOver (Sp T)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of T)))
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P.A.hom
    ((Over.w (y ^ k)).trans (Over.w (1 : baseOver (Sp T) ⟶ P.A)).symm) (spMap jT) e3)

end GlobalTheory.Mum
