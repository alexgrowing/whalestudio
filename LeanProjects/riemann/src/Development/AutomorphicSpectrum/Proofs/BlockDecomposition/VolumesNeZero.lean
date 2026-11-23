import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.VolNe

theorem volumes_ne_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
  (∀ k : ℤ, (selfDualMeasure ψ).real (valBall F k : Set F) ≠ 0) ∧
  (∀ n : ℕ, 1 ≤ n → (multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} ≠ 0) ∧
  (∀ m : ℕ, (LFS.hG ψ).real (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) ≠ 0) := by
  intro F _ _ _ _ _ _ ψ
  refine ⟨fun k => ?_, fun n hn => ?_, fun m => ?_⟩
  · have ho : IsOpen (valBall F k : Set F) := isOpen_valBall k
    have hc : IsCompact (valBall F k : Set F) := isCompact_valBall k
    have hne : (valBall F k : Set F).Nonempty := ⟨0, zero_mem _⟩
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'
  · set H : Set Fˣ := {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} with hH
    have ho : IsOpen H :=
      (isOpen_valBall (n : ℤ)).preimage (Units.continuous_val.sub continuous_const)
    have hne : H.Nonempty := ⟨1, by simp [hH, zero_mem]⟩
    have himg : (Units.val '' H : Set F) = (fun x : F => 1 + x) '' (valBall F (n : ℤ) : Set F) := by
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(h : F) - 1, hh, by ring⟩
      · rintro ⟨x, hx, rfl⟩
        have hy : (1 + x : F) ≠ 0 := by
          intro h0
          have hx1 : x = -1 := by linear_combination h0
          rw [hx1] at hx
          have h1 : normalizedValuation F (-1 : F) ≤ WithZero.exp (-(n : ℤ)) := hx
          rw [Valuation.map_neg, map_one] at h1
          have h2 : (WithZero.exp (0 : ℤ)) ≤ WithZero.exp (-(n : ℤ)) := by
            rw [WithZero.exp_zero]; exact h1
          have h3 := WithZero.exp_le_exp.mp h2
          omega
        refine ⟨Units.mk0 _ hy, ?_, rfl⟩
        simpa [hH] using hx
    have hc : IsCompact H := by
      rw [isOpenEmbedding_units_val.isEmbedding.isCompact_iff, himg]
      exact (isCompact_valBall (n : ℤ)).image (continuous_const.add continuous_id)
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'
  · haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
    have ho := GLnLocal.isOpen_congruenceSubgroup F 2 m
    have hc := GLnLocal.isCompact_congruenceSubgroup F 2 m
    have hne : (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)).Nonempty := ⟨1, one_mem _⟩
    exact (ENNReal.toReal_pos (ho.measure_pos _ hne).ne' hc.measure_lt_top.ne).ne'

end GlobalTheory.CompanionTheory.VolNe
