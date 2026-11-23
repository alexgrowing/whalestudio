import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnZetaGL3GL2DualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationGenericStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerInducedOfFunctionalEquationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL3LiftedWhittakerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2OfInducedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2QuadraticWhittakerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwoStatement

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.DualHolMain

theorem isStd_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ψ : AddChar F Circle), IsStd ψ → IsStd ψ⁻¹ := by
  intro F _ _ _ _ ψ ⟨h1, h2, h3⟩
  have hinv : ∀ x, ψ⁻¹ x = (ψ x)⁻¹ := fun x => AddChar.inv_apply' ψ x
  refine ⟨?_, ?_, ?_⟩
  · have : (ψ⁻¹ : AddChar F Circle) = fun x => (ψ x)⁻¹ := by funext x; exact hinv x
    show Continuous (ψ⁻¹ : AddChar F Circle)
    rw [this]; exact h1.inv
  · exact inv_ne_one.2 h2
  · have : {n : ℤ | IsTrivialOn ψ⁻¹ n} = {n : ℤ | IsTrivialOn ψ n} := by
      ext n
      simp only [Set.mem_setOf_eq, IsTrivialOn, hinv, inv_eq_one]
    rw [← h3, addCharConductor, addCharConductor, this]

theorem isUnit1_cAt {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : IsUnit1 (cAt c v w) := by
  refine ⟨?_, fun x => ?_⟩
  · exact (GroundTheory.Automorphic.GodementSection.continuous_localChar c w).comp
      (Continuous.units_map _ (continuous_adicCompletionMap v w))
  · simp only [cAt, MonoidHom.comp_apply]
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _

theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.HOLV K := by
  intro K _ _ hK D c v W hW Wt e hT
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hν := D.unit v
  have hνi : IsUnit1 (D.ν v)⁻¹ := ⟨hν.1.inv, fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν.2, inv_one]⟩
  have hV := GlobalTheory.T.whittaker_induced_of_functional_equation GlobalTheory.T.functional_equation_generic (Qv v) (GP.psiF v) hψ (D.ν v) (D.ν v)⁻¹ hν hνi
  have h3 : TemperedBoundGL3 W := by
    refine TemperedBoundGL3.span ?_ hW
    rintro _ ⟨W', hW', Φ, hΦ, rfl⟩
    exact GlobalTheory.T.temperedBoundGL3_lifted_whittaker _ _ (D.ν v) _ _ ⟨hψ, hν, ⟨_, hV, hW'⟩, hΦ⟩
  have h2 : TemperedBoundGL2 Wt := by
    rcases hT with ⟨w₁, w₂, i₁, i₂, -, hm, -⟩ | ⟨w, i, -, σ, η, hσ, -, hm, -⟩
    · have hχ := isStd_inv _ _ hψ
      have u₁ := isUnit1_cAt c v w₁
      have u₂ := isUnit1_cAt c v w₂
      have hV' := GlobalTheory.T.whittaker_induced_of_functional_equation GlobalTheory.T.functional_equation_generic (Qv v) (GP.psiF v)⁻¹ hχ _ _ u₂ u₁
      refine TemperedBoundGL2.span ?_ hm
      rintro _ ⟨Φ, h1, h2, h₀, rfl⟩
      obtain ⟨φ, hφ, e⟩ := GlobalTheory.T.compact_whittaker_eq_godement_local _ _ hχ _ _ u₁ u₂ Φ h1 h2
      rw [e]
      exact GlobalTheory.T.temperedBoundGL2_of_induced _ _ _ _ _ u₂ u₁ hV' _ (hV'.stable _ (Submodule.subset_span ⟨φ, hφ, rfl⟩) h₀)
    · refine TemperedBoundGL2.span ?_ hm
      rintro _ ⟨Φ, hΦ, h₀, rfl⟩
      have hc : IsUnit1 (localChar c w) := ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
        rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩
      have hχ := isStd_inv _ _ hψ
      exact GlobalTheory.T.temperedBoundGL2_quadratic_whittaker _ _ hχ.1 hχ.2.1 _ (GlobalTheory.T.nontrivial_galois_place_degree_two K hK v w i σ hσ)
        (continuous_adicCompletionMap v w) σ hσ _ _ hc Φ hΦ h₀
  exact GlobalTheory.T.differentiableOn_zetaGL3GL2_dual _ _ _ _ h3 h2

end GlobalTheory.CompanionTheory.DualHolMain
