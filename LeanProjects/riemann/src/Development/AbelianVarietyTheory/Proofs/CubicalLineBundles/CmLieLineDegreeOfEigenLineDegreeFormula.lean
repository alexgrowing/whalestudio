import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamDegSt_of_degSt : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re := by
  intro hD hU hL E _ _ _ H _ χ hχ _ l c hstar nΨ n' f o La ho
  obtain ⟨-, -, -, -, hΨ, h', -, -, -, tΨ, t', -, -, -, -, -, vΨ, v', -⟩ := ho
  obtain ⟨hb, -, -, ρ, hρ, h1, h2, -⟩ := labK_spec E H l c o.K₁
  exact ⟨fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.AΨ o.oaΨ o.xΨ o.φΨg (psiSet H) o.τΨ (labK c o.K₁) ρ
      hΨ hb.1 hρ h1 tΨ k _ (vΨ k),
    fun k => GlobalTheory.T.normalisedDegree_cmEigenLine_eq hD hU hL E H χ hχ hstar o.K₁ o.A' o.oa' o.x' o.φ'g (psiSet H)ᶜ o.τ' (labK c o.K₁) (-ρ)
      h' hb.1 (by rw [neg_sq, hρ]) h2 t' k _ (v' k)⟩

end GlobalTheory.LamF
