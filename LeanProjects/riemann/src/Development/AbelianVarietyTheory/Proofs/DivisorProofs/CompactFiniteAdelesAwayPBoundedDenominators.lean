import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAwayCpt

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.DenAway

theorem exists_nat_mul_integral_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q →
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  intro p _ Q hQ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun x hx v => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hxa' : (m a : AfP p) * x ∈ intAfP p := hxa
  have e : ((∏ a ∈ t, m a : ℕ) : AfP p) * x = (k : AfP p) * ((m a : AfP p) * x) := by
    rw [hk, Nat.cast_mul]; ring
  rw [e, eval_natCast_mul]
  exact mul_mem (natCast_mem v.1 k) (hxa' v)

end GlobalTheory.DenAwayCpt
