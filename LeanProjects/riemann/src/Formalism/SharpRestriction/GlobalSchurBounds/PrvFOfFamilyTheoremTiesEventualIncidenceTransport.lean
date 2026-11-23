import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem prvF_of_familyTheorem_ties_eventualIncidenceTransport {eps : ℝ} (Fm : FamP eps) (C3 crystallineComparison C22 : ℝ)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison) (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (tVol : StandardLattice.TiesF Fm)
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison := by
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (TaylorLogMetric.AdmF_of Fm (fun x i => UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  exact s10 (product_first_zeroth_parts.AdmF_of Fm C22 100 C₅ h22 h59 (fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1) t10)

end Formalism.MainNotions

end
