import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericMapToModuliBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_map_to_moduli_base : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (B Bg : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (ρ : B ⟶ O.s.T.Z.X), IsPre (genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) (Set.range (O.Φ.C c).π) (dimGr D.what₂.Tau O.N O.j) (genι O.s.T.Z) q jB πB ρ → ∃ β : B ⟶ M.B, β ≫ M.b = ρ ∧ β ≫ strL M = q ∧ β (genericPoint B) = genericPoint M.B ∧ β.residueDegree (genericPoint B) ≠ 0 := by
  first | exact @GlobalTheory.BaseFactor.exists_factor_component | exact GlobalTheory.BaseFactor.exists_factor_component | (intros; apply GlobalTheory.BaseFactor.exists_factor_component <;> assumption)
