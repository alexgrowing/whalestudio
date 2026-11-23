import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem first_type_prime_large_of_record (D : D7) : StandardLattice.GBig D := by
  refine ⟨0, ?_⟩
  have hc := D.ntypes.g_cond 0
  have hg := (D.host.g_prime 0).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g 0 := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have hQ : 1 ≤ D.host.QS := D.host.QS_pos
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

theorem exact_ranks_along_family : ∀ (eps : ℝ) (Fm : FamP eps), (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev) → (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧ ∀ u : (Fm.D x i).what₂.Word, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u) → (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, StandardLattice.volY0 (Fm.D x i) = StandardLattice.massI (Fm.D x i) (Fm.D x i).R.r) → ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro eps Fm h4 ⟨a, ha⟩ ⟨b, hb⟩ C0 Cg cb Cu cT CT
  have key : ∀ x ≥ max (max a b) (Fm.x1 + 1), ∀ i : Fm.Ix x, LocalBesselAndTopKernel.FamilyMidVolume (Fm.D x i) := by
    intro x hx i
    have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hxb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
    obtain ⟨hS, hu⟩ := ha x hxa i
    exact exact_ranks_of_record (Fm.D x i) hS (hb x hxb i) (StandardLattice.factDstar_fam Fm x hx1 i)
      (fun u => h4 x hx1 i (first_type_prime_large_of_record _) hS u (hu u).1 (hu u).2)
  exact ⟨max (max a b) (Fm.x1 + 1), fun x hx i _ => key x hx i⟩

end GlobalTheory
