import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitStandardVector

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.SplitSph

theorem sphs_direct : Ad3.K.QuadraticBaseChangeGL3.Th.SPHS := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 hcond c₁ c₂ h₁ h₂
  rw [GlobalTheory.CompanionTheory.SplitStandardVector.indicator_eq_phiS]
  exact GlobalTheory.CompanionTheory.SplitStandardVector.sphN_WcS_phiS χ c₁ c₂ ⟨hχ, hχ1, hcond⟩ h₁ h₂

end GlobalTheory.CompanionTheory.SphTheta.SplitSph
