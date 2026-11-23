import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTensorPreimmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldOfUniquePrimeStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPullbackResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeFstEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTensorResidueDegreeStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.GenericBaseChange

theorem eq_genericPoint_of_specializes {X : Scheme.{0}} [IsIntegral X] {z : X}
    (h : z ⤳ genericPoint X) : z = genericPoint X :=
  (h.antisymm (genericPoint_specializes z)).eq

theorem baseChange_genericPoint_residueDegree : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (π : Y ⟶ B), IsArithVar q 1 → π (genericPoint Y) = genericPoint B → ∀ (C : RegCover q) [IsIntegral (Limits.pullback π C.ρ)], (Limits.pullback.fst π C.ρ : (Limits.pullback π C.ρ : Scheme.{0}) ⟶ Y) (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = genericPoint Y ∧ (Limits.pullback.fst π C.ρ : (Limits.pullback π C.ρ : Scheme.{0}) ⟶ Y).residueDegree (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = C.deg := by
  intro k _ B Y _ _ q π _ hπ C _
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := C.ρ)
    (genericPoint Y) (genericPoint C.Y) (hπ.trans C.generic.symm)
  have h1 : Limits.pullback.fst π C.ρ (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = genericPoint Y :=
    eq_genericPoint_of_specializes (hz1 ▸ (genericPoint_specializes z).map (Limits.pullback.fst π C.ρ).continuous)
  have h2 : Limits.pullback.snd π C.ρ (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = genericPoint C.Y :=
    eq_genericPoint_of_specializes (hz2 ▸ (genericPoint_specializes z).map (Limits.pullback.snd π C.ρ).continuous)
  have hF := GlobalTheory.T.generic_point_pullback_residue_field GlobalTheory.T.isField_of_unique_prime_stalk π C.ρ (GlobalTheory.T.spec_tensor_preimmersion _ _ _) (h2 ▸ C.finite)
  refine ⟨h1, ?_⟩
  rw [GlobalTheory.T.residue_degree_fst_eq_finrank π C.ρ _ hF, GlobalTheory.T.finrank_tensor_residue_degree]
  change C.ρ.residueDegree (Limits.pullback.snd π C.ρ (genericPoint _)) = _
  rw [h2]; rfl

end GlobalTheory.GenericBaseChange
