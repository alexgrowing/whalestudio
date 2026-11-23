import Formalism.ThetaLiftIndependence.Statement

namespace Formalism.ThetaLiftIndependence

open MulAction in
theorem orbitSum : OrbitSum := by
  classical
  intro H X _ _ _ _ k _ _ F hF
  rw [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_equiv (selfEquivSigmaOrbits H X).symm (fun p => F p.2) F (fun p => rfl),
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hconst : ∀ y : orbit H (Quotient.out o), F y = F (Quotient.out o) := by
    rintro ⟨y, a, rfl⟩
    exact hF a _
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard := card_orbit_mul_card_stabilizer_eq_card_group H (Quotient.out o)
  rw [Nat.card_eq_fintype_card, ← hcard]
  have h1 : (Fintype.card (orbit H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨_, mem_orbit_self (Quotient.out o)⟩⟩ :
      0 < Fintype.card (orbit H (Quotient.out o))).ne'
  have h2 : (Fintype.card (stabilizer H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := stabilizer H (Quotient.out o))).ne'
  push_cast
  field_simp

end Formalism.ThetaLiftIndependence
