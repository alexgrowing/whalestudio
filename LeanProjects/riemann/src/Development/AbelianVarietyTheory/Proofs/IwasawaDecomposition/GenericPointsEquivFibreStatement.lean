import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointsEquivFibre
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_equiv_fibre : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ M.X) [IsClosedImmersion i], IsArithVar (i ≫ M.p) 0 → i (genericPoint Z) = M.j x → ∀ (K : Type) [Field K] (σ : F →+* K), ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃ {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x}, ∀ y, (E y).1.1 ≫ M.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  first | exact @GlobalTheory.TrueGeo.ClosurePts.main | exact GlobalTheory.TrueGeo.ClosurePts.main | (intros; apply GlobalTheory.TrueGeo.ClosurePts.main <;> assumption)
