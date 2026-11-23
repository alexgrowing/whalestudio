import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocalStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.SepLat

theorem kottwitz_lattice_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  intro p _ G Y hsep hdeg
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (Y : G.C) hdeg hsep, GlobalTheory.OrbFinAf.isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (Y : G.C))] with w hA _ hY1
  intro k h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  let γ₀ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  have hγv : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (Y : G.C) := rfl
  have hγi : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = inC G (w.1.adicCompletion ℚ) (Y : G.C) := rfl
  have hγ0 : GlobalTheory.OrbFinAf.IsIntV G w (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hY1
    rw [hγv]; exact hY1
  have hconj : GlobalTheory.OrbFinAf.IsIntV G w (((k⁻¹)⁻¹ * γ₀ * k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
      w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [inv_inv, Units.val_mul, Units.val_mul, hγi]
    exact h1
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ (by rw [hγv]; exact hQm)
    ((hInt _).1 hγ0) k⁻¹ ((hInt _).1 hconj)
  have hcomm : k⁻¹ * U⁻¹ * γ₀ = γ₀ * (k⁻¹ * U⁻¹) := by
    have e : U * (k * γ₀ * k⁻¹) = γ₀ * U := by simpa using hU
    calc k⁻¹ * U⁻¹ * γ₀ = k⁻¹ * U⁻¹ * (γ₀ * U) * U⁻¹ := by group
      _ = k⁻¹ * U⁻¹ * (U * (k * γ₀ * k⁻¹)) * U⁻¹ := by rw [e]
      _ = γ₀ * (k⁻¹ * U⁻¹) := by group
  refine ⟨k⁻¹ * U⁻¹, U, ?_, (hInt _).2 hU1, (hInt _).2 hU2, by group⟩
  show _ * _ = _ * _
  rw [← hγi, ← Units.val_mul, ← Units.val_mul, hcomm]

end GlobalTheory.FinClsLoc.SepLat
