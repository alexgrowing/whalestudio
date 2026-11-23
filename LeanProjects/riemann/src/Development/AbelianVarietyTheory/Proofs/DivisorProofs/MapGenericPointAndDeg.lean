import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelMapSurjectiveBirational
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

set_option autoImplicit false

namespace GlobalTheory.CoverModelDeg

theorem map_genericPoint_and_deg : ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F) (V : GlobalTheory.Mean4O.Cover Y) (M : GlobalTheory.TrueGeo.Model Y) (b : V.X ⟶ M.X), b ≫ M.p = V.p → V.j ≫ b = V.π ≫ M.j → (haveI := M.ar.isIntegral; b (genericPoint V.X) = genericPoint M.X) ∧ Scheme.Hom.residueDegree b (genericPoint V.X) = V.deg := by
  intro F _ _ Y V M b _ hsq
  haveI := M.ar.isIntegral
  haveI := ModelBirational.isPreimmersion_j M
  have hπ : V.π (genericPoint V.G) = genericPoint Y.X := by
    obtain ⟨z, hz⟩ := V.π.surjective (genericPoint Y.X)
    have h : V.π (genericPoint V.G) ⤳ genericPoint Y.X := by
      rw [← hz]; exact (genericPoint_specializes z).map V.π.continuous
    exact (h.antisymm (genericPoint_specializes _)).eq
  have hpt : b (genericPoint V.X) = genericPoint M.X := by
    rw [← CoverDeg.j_genericPoint V, ← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hπ,
      ModelBirational.j_genericPoint M]
  refine ⟨hpt, ?_⟩
  have h1 := CurveDegreesCompare.residueDegree_comp V.j b (genericPoint V.G)
  have h2 := CurveDegreesCompare.residueDegree_comp V.π M.j (genericPoint V.G)
  rw [hsq, h2, CoverDeg.j_residueDegree, mul_one, CoverDeg.j_genericPoint V,
    CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks M.j, one_mul] at h1
  exact h1.symm

end GlobalTheory.CoverModelDeg
