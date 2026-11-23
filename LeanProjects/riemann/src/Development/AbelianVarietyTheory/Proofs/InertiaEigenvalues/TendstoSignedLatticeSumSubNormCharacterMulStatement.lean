import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A, B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 - chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | exact GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | (intros; apply GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible <;> assumption)
