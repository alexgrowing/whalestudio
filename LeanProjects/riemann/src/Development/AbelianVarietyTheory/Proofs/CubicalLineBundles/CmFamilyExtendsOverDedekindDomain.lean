import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekindStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem isFam_extends_dedekind :
    Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ω' : K) (C' : Ell H K ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp K)) (m : SABMap T'.t T.t (spMap (algebraMap R K))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap R K) φ → IsFam C' T' h L ψ' → ∃ ψ : L → (C.P.A ⟶ T.t.G), IsFam C T h L ψ ∧ ∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left := by
  intro hL hD E _ _ _ H R K _ _ _ _ _ ω C D h T L ω' C' φ T' m ψ' hφ hψ'
  have key : ∀ a : L, ∃ F : C.P.A ⟶ T.t.G, (ψ' a).left ≫ m.φ = φ ≫ F.left := fun a => by
    obtain ⟨F, -, hF, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hD R K C.P.A T.t.G C'.P.A T'.t.G
      φ m.φ C.P.isAb T.ab hφ.2.1.2.1 m.cart (ψ' a) (hψ'.1 a).isMonHom
    exact ⟨F, hF⟩
  choose ψ hψ using key
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H R ω C D h T L ψ K ω' C' (algebraMap R K) φ T' m ψ'
    (IsFractionRing.injective R K) hφ hψ hψ', hψ⟩

end GlobalTheory
