import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWhittakerIwasawaInvariance
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem W_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.W (dg2 a a * g) = omW m a * m.W g := by
  intro K _ _ h2 c v m hok a g
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    exact GlobalTheory.CompanionTheory.SplitCentre.sCen (Qv v) _ hχc hχ1 _ _
      (GlobalTheory.CompanionTheory.LocalWhittakerNorm.isUnit1_cAt' c v w₁) (GlobalTheory.CompanionTheory.LocalWhittakerNorm.isUnit1_cAt' c v w₂)
      Φ ⟨hok.2.1, hok.2.2⟩ a g
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, hΦ⟩ := hok
    exact GlobalTheory.CompanionTheory.WeilCentral.wCen (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη (localChar c w) Φ hΦ a g

end GlobalTheory.CompanionTheory.CenTheta
