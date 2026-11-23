import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2ZStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem isFam_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  intro hE F _ _ _ hF s N L hs hN hL ι act α Ch κ hα hC
  rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
  intro i γ τ
  have htw : twist N L (α (act i γ)) = mulMat (twist N L (α i)) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hα]; exact GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z F N L (α i) γ hL.2
  have h := GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform hE F hF s N (twist N L (α i)) hs hN (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α i) hL) κ γ (Ch i)
    (Ch (act i γ)) τ ⟨_, GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α (act i γ)) hL, htw⟩ (hC i γ τ)
  rw [zpow_natCast]
  beta_reduce
  rw [h, htw]

end GlobalTheory.HilbFam
