import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchOfCoordinatesAndCount
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.ValuationDetBasisChangeZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.UnitaryNorms.UnramT

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

theorem locBases {D : D7} {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have hL := bwB_clsCrd_lat D u i hi c
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  obtain ⟨d0, hd0, hle0⟩ := exists_le_bnd _ hL
  have hLd : Ld D u i hi c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL
  refine ⟨exists_isLocBasis _ _ _ (fg_of_le_bnd hd hLd) hLd_sp, fun v => exists_isLocBasis _ _ _ ?_ ?_⟩
  · refine fg_of_le_bnd (mul_ne_zero hd hd0) (sup_le (hle0.trans (bnd_mono d0 d)) ?_)
    refine (Submodule.smul_le_right.trans hLd).trans ?_
    rw [mul_comm]
    exact bnd_mono d d0
  · exact eq_top_iff.2 (hL.span_eq_top ▸ Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left))

def OntoAll (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ T : Forms0 D u, admS D u → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
    ∀ B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E,
      (∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) →
      (∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) →
      OntoAt T w v B B'

theorem second_branch_coordinates_of_surjectivity {D : D7} {u : D.what₂.Word} (h : OntoAll D u) : SecondBranchCoordinates D u := by
  intro T hA w hw hs v hb
  choose B hB using fun c => (locBases T.atT 0 (Nat.zero_le _) c).1
  choose B' hB' using fun c => (locBases T.atT 0 (Nat.zero_le _) c).2 v
  refine ⟨B, B', hB, hB', fun c => ?_, h T hA w hw hs v hb B B' hB hB'⟩
  exact V0.det_basis_change_unit_zero D u T (Formalism.L2.Host.second_unramified_condition_holds (D := D) (u := u) T.atT) w hw hs v 0 (Nat.zero_le _) rfl c
    (B c) (B' c) (hB c) (hB' c)

theorem second_branch_of_surjectivity (hO : ∀ (D : D7) (u : D.what₂.Word), OntoAll D u)
    (hd : ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → admS D u → DuCount D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_coordinates_and_count (fun D u => second_branch_coordinates_of_surjectivity (hO D u)) hd

end Formalism.L2.GlobalTheoryTheory.LemB
