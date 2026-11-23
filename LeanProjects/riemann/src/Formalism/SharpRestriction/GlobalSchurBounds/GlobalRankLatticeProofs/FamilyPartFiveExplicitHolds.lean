import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LogWeightMinusLogBBound
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LogFactorialProductDifference
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LogVandermondeVariationGeneric

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem part_five_explicit_eventually (eps C0 CY : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → VandermondeCountExplicitBound D sc C0 CY := by
  obtain ⟨xa, ha⟩ := part_five_lower_eventually eps C0 CY heps
  obtain ⟨xb, hb⟩ := logXuD_upper_bound_eventually eps C0 CY heps
  refine ⟨max xa xb, fun D sc he hx h2 h3 _ _ h4B => ?_⟩
  have h5 : Conclusion5Sharp D sc C0 CY := fun Δ w hA u =>
    ⟨ha D sc he (le_trans (le_max_left _ _) hx) h2.2.2.1 h2.2.1 h3 h4B Δ w hA u,
      hb D sc he (le_trans (le_max_right _ _) hx) h2.2.2.1 h2.2.1 h3 h4B Δ w hA u⟩
  exact part_five_explicit_of_propositions D sc C0 CY h5 (vandermonde_variation_holds D sc C0 CY)

theorem family_part_five_explicit_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyVandermondeCountBound Fm := by
  intro h2 h3 _ h4B C0 CY
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := part_five_explicit_eventually eps C0 CY heps
  obtain ⟨x1, hx1⟩ := h4B C0
  refine ⟨max x0 x1, fun x hx hxx i => ?_⟩
  exact hx0 (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i)
    (by rw [Fm.L_x x i hxx]; exact le_trans (le_max_left _ _) hx) (h2 x i) (h3 x i) (local_index_formulas_and_bounds _)
    (levelPartB_holds _) (hx1 x (le_trans (le_max_right _ _) hx) hxx i)

end Formalism.MainNotions.StandardLattice
