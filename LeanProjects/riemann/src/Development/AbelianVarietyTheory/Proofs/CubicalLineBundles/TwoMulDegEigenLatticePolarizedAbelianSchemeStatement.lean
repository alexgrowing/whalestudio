import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianScheme
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  first | exact @GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | exact GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | (intros; apply GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV <;> assumption)
