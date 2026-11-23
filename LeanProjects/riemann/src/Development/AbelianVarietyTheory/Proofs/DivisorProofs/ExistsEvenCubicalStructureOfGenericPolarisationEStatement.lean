import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationE
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  first | exact @GlobalTheory.Mum.exists_even_package_of_ext | exact GlobalTheory.Mum.exists_even_package_of_ext | (intros; apply GlobalTheory.Mum.exists_even_package_of_ext <;> assumption)
