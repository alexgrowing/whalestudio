import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaOrthTotal

theorem eq_zero_of_orthogonal_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 q hq hquasi horth
  obtain ⟨f₀, hne, h₀⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  have hq' : ∀ γ ∈ ratL T S, ∀ w, q (γ + w) = ψ (-(symplOH S T γ w)) * q w := by
    intro γ hγ w
    obtain ⟨γ', rfl⟩ := hγ
    exact hquasi γ' w
  have horth' : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (q x) ∂μ = 0 := by
    intro w
    have h := horth _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ h₀)
    have e : (fun x => heisO ψ S T w f₀ x * star (q x)) = fun x => (starRingEnd ℂ) (q x * star (heisO ψ S T w f₀ x)) := by
      funext x
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [e, integral_conj, h, map_zero]
  exact GlobalTheory.HeisTotal.eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann
    f₀ q h₀.cont hq (GlobalTheory.HeisTotal.quasi_of_mem h₀) hq' hne μ 𝓕 hμ h𝓕 horth'

end GlobalTheory.ThetaOrthTotal

end
