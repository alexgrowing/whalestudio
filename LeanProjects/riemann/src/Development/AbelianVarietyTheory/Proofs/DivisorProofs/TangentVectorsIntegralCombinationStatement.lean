import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsIntegralCombination
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseOfIntegralSolutionsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_integral_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V Fr : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] (xV : Sp V ⟶ X) (m : ℕ) (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left)), (∀ i, IsTanAtG t xV (v i)) → (∀ (cf : Fin m → Fr) (u : Sp (DualNumber V) ⟶ t.G.left), IsTanAtG t xV u → IsCombAtG t (spMap (algebraMap V Fr) ≫ xV) (fun i => spMap (dualMap (algebraMap V Fr)) ≫ v i) cf (spMap (dualMap (algebraMap V Fr)) ≫ u) → ∀ i, ∃ a : V, algebraMap V Fr a = cf i) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (ψ : V →+* C), (∀ z, ‖ψ z‖ ≤ 1) → (∃! xO : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO = spMap ψ ≫ xV) → ∀ i, grNorm t (spMap ψ ≫ xV) (latDR t (spMap ψ ≫ xV)) (fun k => spMap (dualMap ψ) ≫ v k) i = 1 := by
  first | exact @GlobalTheory.SatTanNorm.grNorm_latDR_eq_one_of_saturated | exact GlobalTheory.SatTanNorm.grNorm_latDR_eq_one_of_saturated | (intros; apply GlobalTheory.SatTanNorm.grNorm_latDR_eq_one_of_saturated <;> assumption)
