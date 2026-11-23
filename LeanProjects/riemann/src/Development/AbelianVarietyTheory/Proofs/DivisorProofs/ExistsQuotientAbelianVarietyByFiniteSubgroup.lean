import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExistStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quotient_finite :
    ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i →
      IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧
        ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  intro K _ A H _ i hi hmono hfin
  have hflat : Flat H.hom := inferInstance
  obtain ⟨B', inst, q, -, hB, hq, hqfin, -, hqsurj, -, hsq⟩ :=
    AbQuotientAny.exists_quotient_abelianScheme K A.X H i A.ab hi hmono hfin hflat
  obtain ⟨g, hg⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K B' hB
  let B : AbVar K := ⟨B', hB, g, hg⟩
  refine ⟨B, Hom.mk (B := B) q, ⟨hqfin, hqsurj⟩, fun T x => ⟨fun hx => ?_, ?_⟩⟩
  · have e : x ≫ q = (1 : T ⟶ A.X) ≫ q := by
      rw [MonObj.one_comp]; exact hx
    have h1 := hsq.lift_fst x 1 e
    have h2 := hsq.lift_snd x 1 e
    rw [MonObj.comp_mul, h2, _root_.mul_one, ← Category.assoc] at h1
    exact ⟨_, h1⟩
  · rintro ⟨y, rfl⟩
    have hw := congrArg (fun f => lift y (1 : T ⟶ A.X) ≫ f) hsq.w
    rw [← Category.assoc, ← Category.assoc, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst,
      _root_.mul_one] at hw
    rw [MonObj.one_comp] at hw
    exact hw

end GlobalTheory.AV.AbVar
