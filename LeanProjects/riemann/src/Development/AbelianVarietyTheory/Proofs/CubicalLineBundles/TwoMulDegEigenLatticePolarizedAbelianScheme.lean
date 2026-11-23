import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEigLatEqOfIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfPolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeOfIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem two_mul_deg_eigLat_of_polAV : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  intro hD hT hL E _ _ _ H _ χ hχ K _ _ ρ P act hbal hs hρ ht F h hh τ hτ
  obtain ⟨T, e, -, hlin, hlam⟩ := exists_pat_of_polAV hL E H (𝓞 K) P act hbal
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  obtain ⟨h₁, hh₁⟩ := (LieMetric.exists_unique_isHerm hT hL K T.pol F₁).1
  have ht₁ : HasType H T.t.act ρ 1 0 := hasType_of_iso E H (𝓞 K) _ _ _ _ e ρ 1 0 hlin ht
  rw [← deg_eigLat_eq_of_iso hT hL K T.pol P F₁ F h₁ h (𝓞 E) T.t.act act e hh₁ hh hlin hlam τ]
  exact hD E H χ hχ K ρ T hs hρ ht₁ F₁ h₁ hh₁ τ hτ

end GlobalTheory.LamF
