import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem isUnit_of_isUnit_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A)
    (h : IsUnit (A.sharp a)) : IsUnit a := by
  have hu : IsUnit (A.aToU1 a) := by
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq]
    exact h.map _
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨b, rfl⟩ := hsurj v
  have hmem : a * b - 1 ∈ Ideal.span {A.pi} := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self]
  have hjac : Ideal.span {A.pi} ≤ (⊥ : Ideal A.A).jacobson := by
    haveI : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
    exact IsAdicComplete.le_jacobson_bot _
  have hunit := Ideal.mem_jacobson_bot.mp (hjac hmem) 1
  rw [mul_one, sub_add_cancel] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end GlobalTheory.CompanionTheory.Untilt
