import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPreservesIntegerRingStatement
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigKQ_mem_intKQ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intKQ p K r, sigKQ p K r x ∈ intKQ p K r := by
  have hle : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show sigKQ p K r (inclK p K r a) ∈ intKQ p K r
      have : sigKQ p K r (inclK p K r a) = inclK p K r a := by
        exact DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id ℚ_[p] K) (frobQ p r)) (a : K)
      rw [this]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · show sigKQ p K r (inclQ p K r b) ∈ intKQ p K r
      have hb : GlobalTheory.LKLoc.frobR p (Q0 p) r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r :=
        GlobalTheory.T.frobenius_preserves_integer_ring p (Q0 p) r b b.2
      have : sigKQ p K r (inclQ p K r b) = inclQ p K r (⟨_, hb⟩ : GlobalTheory.LKLoc.intR p (Q0 p) r) := by
        simp [sigKQ, inclQ, Algebra.TensorProduct.map_tmul]
        rfl
      rw [this]
      exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact fun x hx => hle hx

theorem sigRes_mem_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ),
    ∀ g ∈ Kres p K n r, sigRes p K n r g ∈ Kres p K n r := by
  intro p _ K n r g hg
  obtain ⟨h, rfl⟩ := hg
  let f : intKQ p K r →+* intKQ p K r :=
    (sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r) (sigKQ_mem_intKQ p K r)
  refine ⟨GeneralLinearGroup.map f h, ?_⟩
  ext i j
  rfl

end GlobalTheory.LKRes
