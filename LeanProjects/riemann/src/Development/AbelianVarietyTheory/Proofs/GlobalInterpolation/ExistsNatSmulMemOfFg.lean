import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS

namespace GlobalTheory.FinitelyGeneratedNatMultiple

theorem exists_nat_smul_mem_of_fg {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (NumberField.RingOfIntegers E) W]
    {M N : Submodule (NumberField.RingOfIntegers E) W}
    (hM : GlobalTheory.ThetaMove.Full M) (hN : Submodule.FG N) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : NumberField.RingOfIntegers E) • x ∈ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have hM' : ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : NumberField.RingOfIntegers E) • x ∈ M := hM
  choose n hn0 hn using hM'
  refine ⟨∏ y ∈ s, n y, Finset.prod_pos fun y _ => hn0 y, fun x hx => ?_⟩
  have hle : Submodule.span (NumberField.RingOfIntegers E) (s : Set W) ≤
      M.comap (LinearMap.lsmul (NumberField.RingOfIntegers E) W
        ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hy)
    show ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E) • y ∈ M
    rw [hk, mul_comm, Nat.cast_mul, mul_smul]
    exact M.smul_mem _ (hn y)
  exact hle hx

end GlobalTheory.FinitelyGeneratedNatMultiple
