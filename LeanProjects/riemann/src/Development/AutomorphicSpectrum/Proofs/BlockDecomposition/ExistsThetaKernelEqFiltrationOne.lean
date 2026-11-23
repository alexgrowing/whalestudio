import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernelsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfectAlg

theorem exists_theta_mod {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧
      RingHom.ker θ = A.Fil n 1 := by
  obtain ⟨hsurj, hker, -, -⟩ := GlobalTheory.T.quotient_maps_surjective_with_kernels A n
  refine ⟨((Ideal.quotEquivOfEq hker).toRingHom.comp
      (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom).comp
      (Ideal.Quotient.mk (A.Fil n 1)), fun x => ?_, ?_⟩
  · have h1 : A.uToQ n (A.th x) = Ideal.Quotient.mk (A.Fil n 1) (A.toAcr n x) := by rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← h1, ← RingHom.quotientKerEquivOfSurjective_apply_mk hsurj, RingEquiv.symm_apply_apply,
      Ideal.quotEquivOfEq_mk]
  · ext y
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff _ (RingEquiv.injective _), map_eq_zero_iff _ (RingEquiv.injective _),
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.CompanionTheory.PerfectAlg
