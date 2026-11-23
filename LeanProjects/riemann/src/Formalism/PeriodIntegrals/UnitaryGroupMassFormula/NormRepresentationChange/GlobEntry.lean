import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_entry (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (a : Fin (D.R.rS + 1)) (h : a.val + 1 < D.R.rS + 1) :
    ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = fmat D G n a ⟨a.val + 1, h⟩ * δ := by
  have ha : a.val < D.R.rS := by omega
  have hf : fmat D G n a ⟨a.val + 1, h⟩ =
      G.fl.coefX (n (frame G ⟨a.val + 1, h⟩) - frame G ⟨a.val + 1, h⟩) ⟨a.val, ha⟩ := by
    simp only [fmat, dif_pos ha]
    rw [if_neg (by intro e; have := congrArg Fin.val e; simp at this), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  by_cases hr : a.val + 1 < D.R.rS
  · have hfi : frame G ⟨a.val + 1, h⟩ = G.fl.e ⟨a.val + 1, hr⟩ := by
      rw [show (⟨a.val + 1, h⟩ : Fin (D.R.rS + 1)) = (⟨a.val + 1, hr⟩ : Fin D.R.rS).castSucc from Fin.ext rfl,
        frame_castSucc]
    rw [hfi]
    apply frac_lemma D _ (-((D.R.rS : ℤ) - ((a.val + 1 : ℕ) : ℤ)))
    intro x hx
    have hxe : x • G.fl.e ⟨a.val + 1, hr⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨a.val + 1, hr⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨a.val + 1, hr⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hc := (coefX_of_mem_XS D G.fl hn1).2 ⟨a.val, ha⟩
    have hd : n (G.fl.e ⟨a.val + 1, hr⟩) - G.fl.e ⟨a.val + 1, hr⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨a.val + 1, hr⟩) =
        x • (G.fl.e ⟨a.val + 1, hr⟩ + (n (G.fl.e ⟨a.val + 1, hr⟩) - G.fl.e ⟨a.val + 1, hr⟩)) := by
      rw [map_smul]; congr 1; abel
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e,
      if_neg (by intro e; have := congrArg Fin.val e; simp at this), zero_add] at hc
    have hexp : -((D.R.rS : ℤ) - ((a.val + 1 : ℕ) : ℤ)) - 1 =
        -((D.R.rS : ℤ) - (((⟨a.val, ha⟩ : Fin D.R.rS) : ℕ) : ℤ)) := by
      push_cast; ring
    rw [hexp]
    exact hc
  · have hfz : frame G ⟨a.val + 1, h⟩ = G.fl.z := by
      rw [show (⟨a.val + 1, h⟩ : Fin (D.R.rS + 1)) = Fin.last _ from Fin.ext (by simp; omega), frame_last]
    rw [hfz]
    apply frac_lemma D _ 0
    intro x hx
    rw [zpow_zero] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hc := (coefX_of_mem_XS D G.fl hv).2 ⟨a.val, ha⟩
    have hexp : (0 : ℤ) - 1 = -((D.R.rS : ℤ) - (((⟨a.val, ha⟩ : Fin D.R.rS) : ℕ) : ℤ)) := by
      push_cast; omega
    rw [hexp, ← Algebra.smul_def]
    exact fi_smul _ o hc

theorem stepGlob (D : D7) : StepGlob D := by
  intro Λ T G n hn hXS hz δ hδ
  have hmem : sgUp (fmat D G n) * δ ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    unfold sgUp
    rw [Finset.sum_mul]
    apply Subring.sum_mem
    intro a _
    split_ifs with h
    · obtain ⟨o, ho⟩ := glob_entry D Λ G n hn hXS hz a h δ hδ
      exact ⟨o, ho⟩
    · rw [zero_mul]; exact Subring.zero_mem _
  obtain ⟨o, ho⟩ := hmem
  exact ⟨o, ho⟩

end PI.NRCW
