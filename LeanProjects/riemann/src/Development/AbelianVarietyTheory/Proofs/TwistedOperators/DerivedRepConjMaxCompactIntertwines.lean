import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
open scoped InnerProductSpace

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta
open GlobalTheory.SmoothGlob (lieSet)

namespace GlobalTheory.GKLie

theorem dRep_conj_Kset (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) :
    ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H,
      Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v →
      Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  intro κ hκ X hX v hv
  have h1 : κᴴ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ.1
  have h2 : κ * κᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ.1
  have hu : IsUnit κ := IsUnit.of_mul_eq_one _ h2
  have hinv : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det κ).1 hu)
  have hκU : κ ∈ UJset ε := by
    change κᴴ * Jm ε * κ = Jm ε
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    change (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']
  have hE : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε := fun t =>
    GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t
  have hinvU : κ⁻¹ ∈ UJset ε := by
    have hκinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h1
    rw [hκinv]
    change κᴴᴴ * Jm ε * κᴴ = Jm ε
    rw [Matrix.conjTranspose_conjTranspose, hκ.2, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfun : (fun t : ℝ => ρ (NormedSpace.exp (t • (κ * X * κ⁻¹))) (ρ κ v)) =
      fun t : ℝ => ρ κ (ρ (NormedSpace.exp (t • X)) v) := by
    funext t
    have hc : NormedSpace.exp (t • (κ * X * κ⁻¹)) = κ * NormedSpace.exp (t • X) * κ⁻¹ := by
      rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc]
    have hA : κ * NormedSpace.exp (t • X) * κ⁻¹ ∈ UJset ε := hmul _ (hmul _ hκU _ (hE t)) _ hinvU
    rw [← ContinuousLinearMap.comp_apply, ← hρ.2 _ hA _ hκU, Matrix.mul_assoc _ κ⁻¹ κ, hinv, Matrix.mul_one,
      hρ.2 _ hκU _ (hE t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [hfun]
  have hd := (differentiableAt_orbit hv hX).hasDerivAt
  have hL : HasFDerivAt (ρ κ) ((ρ κ).restrictScalars ℝ) (ρ (NormedSpace.exp ((0 : ℝ) • X)) v) :=
    ((ρ κ).restrictScalars ℝ).hasFDerivAt
  exact (hL.comp_hasDerivAt (0 : ℝ) hd).deriv

end GlobalTheory.GKLie
