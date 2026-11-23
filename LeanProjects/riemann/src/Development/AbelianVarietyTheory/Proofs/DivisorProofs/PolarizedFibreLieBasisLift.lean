import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.LieHt

theorem exists_isLieBasis_isVecOver_of_isPolFibre : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (K'' : Type) [Field K''] [NumberField K''] [Algebra K K''] (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left), GlobalTheory.IsPolFibre (algebraMap K K'') F.P₀ P ψ → ∃ v' : Fin F.P₀.g → (epsR K'' ⟶ P.A), (∀ k, GlobalTheory.IsVecOver (algebraMap K K'') ψ (F.v k) (v' k)) ∧ IsLieBasis v' := by
  intro K _ _ F K'' _ _ _ P ψ h
  have hs : Smooth F.P₀.A.hom := F.P₀.isAb.smooth
  obtain ⟨v', hb, hv⟩ := GlobalTheory.exists_isLieBasis_baseChange K K'' (algebraMap K K'') F.P₀.A P.A ψ h.2.1 hs
    F.P₀.g F.v F.basis
  exact ⟨v', hv, hb⟩

end GlobalTheory.LieHt
