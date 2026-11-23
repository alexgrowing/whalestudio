import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusAverageIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCentralCharacterAtZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormGlobalCentralScalarEqOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundNumberField
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

theorem centralScalar_twisted_data {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} (n : ℤ) (t : ℝ)
    (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (x : ∀ v : Sv, (Qv v.1)ˣ) (z : Jd) :
    u0 n t (twM M Sv m x) z = u0 n t M z := by
  have h : ∀ v, om0 (twM M Sv m x v) (Ad3.R.lc v z) = om0 (M v) (Ad3.R.lc v z) := by
    intro v
    simp only [twM]
    cases M v <;> rfl
  simp only [u0, h]

theorem theta_central_character {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K}
    (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl)
    (z : Jd) (g : G2) : th0 R Sv n t M (dg2 z z * g) = u0 n t M z * th0 R Sv n t M g := by
  simp only [th0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := GlobalTheory.T.theta_central_character_at_zero K h2 c n t (twM M Sv m x) (GlobalTheory.CompanionTheory.TorusAverage.admissible_twisted_local_data hM Sv m x) z g
  rw [centralScalar_twisted_data] at this
  simp only [this]
  ring

def CenFix (K : Type) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) c n t S, AdmK DK c n t S → ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ z : Jd,
    ∃ u : ℂ, ‖u‖ = 1 ∧ (∀ g, WM n t M (dg2 z z * g) = u * WM n t M g) ∧
      ∀ (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (κ₀ : ℂ),
        (∀ g ∈ Gp M, HasSum (fun α : ℚˣ => κ₀ * WM n t M (dg2 (pri α) 1 * g))
          (thA R Sv n t M g - th0 R Sv n t M g)) →
        (∀ g ∈ Gp M, ∀ x : 𝔸[ℚ], th0 R Sv n t M (uni2 x * g) = th0 R Sv n t M g) →
        (∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → ∀ g ∈ Gp M,
          thA R Sv n t M (dia2 γ * g) = thA R Sv n t M g) →
        ∀ g ∈ Gp M, th0 R Sv n t M (dg2 z z * g) = u * th0 R Sv n t M g

end GlobalTheory.CompanionTheory.CenTheta
