import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle

theorem pair_single : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  intro F E _ _ _ _ _ σ M J hJ n ψf c c₀ i₀ x s ρ
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have key : ∀ a, hR (Af F) σ J (fun i => if i = i₀ then x else 0) (ratTuple J s ρ a) =
      sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    intro a
    have hv : ∑ j, J i₀ j * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = algebraMap (𝓞 E) E (ρ i₀ a) := by
      have h1 : (J *ᵥ (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a))) i₀ =
          algebraMap (𝓞 E) E (ρ i₀ a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      simpa [Matrix.mulVec, dotProduct] using h1
    unfold hR Formalism.UG.hform
    rw [Finset.sum_eq_single i₀]
    · simp only [if_true, JR, ratTuple, Matrix.map_apply]
      rw [← hv]
      simp only [map_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro i _ hi
      simp [hi]
    · simp
  have hz : ∀ (c' : Fin n) (a : Fin n), c' ≠ c₀ →
      hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) = 0 := by
    intro c' a hc
    simp [hR, Formalism.UG.hform, hc]
  have hin : ∀ a b, ((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) a b = inclR (Af F) (c.1 a b) := fun a b => rfl
  have htr : Matrix.trace (((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gram2 σ J (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ)) =
      sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hin, gram2]
    have h2 : ∀ a, ∑ c', inclR (Af F) (c.1 a c') *
        hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) =
        inclR (Af F) (c.1 a c₀) *
          (sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a))) := by
      intro a
      rw [Finset.sum_eq_single c₀]
      · simp only [true_and]
        rw [key a]
      · intro c' _ hc
        rw [hz c' a hc, mul_zero]
      · simp
    simp only [h2]
    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_mul]
    ring
  unfold pairB
  rw [htr]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle
