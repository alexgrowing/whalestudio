import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalRingCardinality.HostCls
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.HalfDiffInt

theorem prime_not_dvd_discr (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ¬ p ∣ (discr D.host.E).natAbs :=
  UpperTheory.Ram.not_dvd_natAbs_discr D.host hp h2 hq hd

theorem absNorm_dvd_discr (D : D7) : Ideal.absNorm D.host.𝔟 ∣ (discr D.host.E).natAbs := by
  have htow := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.K (𝓞 D.host.K)
    D.host.E (𝓞 D.host.E)
  rw [htow, D.host.𝔟_spec.1, map_mul, mul_assoc]
  exact Dvd.intro _ rfl

theorem absNorm_coprime (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    Nat.Coprime (Ideal.absNorm D.host.𝔟) p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  exact prime_not_dvd_discr D hp h2 hq hd (dvd_trans h (absNorm_dvd_discr D))

theorem inv_integral_off (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro a ha
  have hcop := absNorm_coprime D hp h2 hq hd
  have hne : D.host.𝔟 ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot, Nat.coprime_zero_left] at hcop
    exact hp.one_lt.ne' hcop
  refine ⟨Ideal.absNorm D.host.𝔟, hcop, ?_⟩
  have ha' : a ∈ ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
    have : a ∈ D.host.AA0 := ha
    rwa [Host.AA0] at this
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hne)] at ha'
  have hs := ha' _ (FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E)
    (Ideal.absNorm_mem D.host.𝔟))
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 hs
  refine ⟨x, ?_⟩
  rw [hx, map_natCast, mul_comm]

theorem class_c0_prime_not_exceptional {R : Ranks} (H : Host R) {p : ℕ} (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d :=
  let k := (primeClass_eq_inert_iff H.toHostRaw).1 h
  ⟨k.1, k.2.1, k.2.2.1⟩

end GlobalTheory.TwV.HalfDiffInt

namespace GlobalTheory.TwV

theorem halfDiffInv_integral_at_split : ∀ (D : D7) (T p : ℕ), GIdx D.host T p → (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) := by
  intro D T p hg
  obtain ⟨h2, hq, hd⟩ := HalfDiffInt.class_c0_prime_not_exceptional D.host hg.2.2.1
  exact HalfDiffInt.inv_integral_off D hg.1 h2 hq hd

end GlobalTheory.TwV

end
