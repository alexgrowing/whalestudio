import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieWordExpansion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieWordExpansionStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  intro D θ hθ hPr N τ f hf hty x
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hty
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (N.M.enum τ) hE'
  subst hl he
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (N.M.ε τ) (N.M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ)) _ (N.M.fr τ) P'
    (N.M.fr_unit τ) hP' (N.M.fr_gram τ) hJ' _ _ (N.M.σ τ) σ' (N.M.ds τ) hD'
  have t := GlobalTheory.TypeSum.hasTypeAll_transport _ H' (N.M.H τ) (fun g => σ' (P' * g * P'⁻¹)) (N.M.σ τ)
    (gramAt D N.V τ) (Formalism.REAL.Jm (N.M.ε τ)) (N.M.fr τ) (isUnit_gram (N.M.fr_unit τ) (N.M.fr_gram τ))
    (N.M.fr_unit τ) (N.M.fr_gram τ) U hU (fun g => f (x * atTau θ N.V τ g))
    (GlobalTheory.TypeSum.hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := t
  exact ⟨S, v, ℓ, C, hS, hc, h⟩
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model <;> assumption)
end
