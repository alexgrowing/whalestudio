import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomCharpoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace FibreNormDehomCharpoly

theorem finiteDimensional_pullField (hR : PullRatiosAlgebraic.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ}
    {L : Fin (D + 1) → MRing ι} (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB : Birational y) (he : ∀ k, 1 ≤ e k)
    (hL : ∀ j, IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    FiniteDimensional (pullField y L) Ω := by
  classical
  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  set P := pullField y L
  set S : Set Ω := {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = y p / y q} with hS
  have hSf : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) => y pq.1 / y pq.2).subset
    (by rintro _ ⟨p, q, -, rfl⟩; exact ⟨(p, q), rfl⟩)
  have : Finite S := hSf.to_subtype
  have hSi : ∀ x ∈ S, IsIntegral P x := by
    rintro _ ⟨p, q, hpq, rfl⟩
    exact (hR K ι Ω y D e L hrel' he hL hz p q hpq).isIntegral
  have hfd : FiniteDimensional P (IntermediateField.adjoin P S) := IntermediateField.finiteDimensional_adjoin hSi
  have htop : IntermediateField.adjoin P S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ blockFnField y := (PullFormsGeneric.blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top
    have hle : blockFnField y ≤ (IntermediateField.adjoin P S).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      exact fun t ht => IntermediateField.subset_adjoin P S ht
    exact hle hx
  have hfd' : FiniteDimensional P (⊤ : IntermediateField P Ω) := htop ▸ hfd
  exact (IntermediateField.topEquiv (F := P) (E := Ω)).toLinearEquiv.finiteDimensional

end FibreNormDehomCharpoly

open FibreNormDehomCharpoly in

theorem FibreNormDehomCharpoly.proof (hG : PullFormsGeneric.Statement) (hR : PullRatiosAlgebraic.Statement)
    (hI : PullSectionIntegral.Statement) (hC : DehomCharpolyForms.Statement) : FibreNormDehomCharpoly.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz
  classical
  have hfin : FiniteDimensional (pullField y L) Ω := finiteDimensional_pullField hR hA hB he hL hz
  refine ⟨hfin, fun τ s hs j hj => ?_⟩
  set l : Fin (D + 1) → Ω := fun i => aeval y (L i) with hl
  have hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0 :=
    hG K ι Ω y D e L hA hB he hL hz
  have hne : ∀ k, l k ≠ 0 := fun k h0 =>
    X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X]; exact h0))
  have hint : ∀ k, s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) ∈
      integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω := by
    intro k
    have h : s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) = s / l k ^ (q * τ) := by
      rw [div_pow, div_mul_div_comm, mul_comm (l j ^ (q * τ)), mul_div_mul_right _ _ (pow_ne_zero _ (hne j))]
    rw [h]
    exact hI K ι Ω y D e L q hA hB he hL hz τ s hs k (hne k)
  obtain ⟨c, hc0, hch, hcp, hcn⟩ := hC Ω D l (pullField y L) rfl hgen j (q * τ) (s / l j ^ (q * τ)) hint
  exact ⟨c, ⟨hj, hfin, hc0, hch, hcp⟩, fun hs0 => hcn (div_ne_zero hs0 (pow_ne_zero _ hj))⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
