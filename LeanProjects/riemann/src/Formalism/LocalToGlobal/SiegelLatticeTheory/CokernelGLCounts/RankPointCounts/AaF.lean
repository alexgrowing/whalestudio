import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.GlobEntry
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.StepGram

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable (D : D7)

abbrev aaF (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem entry_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) (hcb : c < b) : ∀ x ∈ aaF D b, x * fmat D G n c b ∈ aaF D c := by
  have hc : c.val < D.R.rS := by have := b.isLt; omega
  have hf : fmat D G n c b = G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, hc⟩ := by
    simp only [fmat, dif_pos hc]
    rw [if_neg (ne_of_lt hcb), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  have haF : aaF D c = aaI D ⟨c.val, hc⟩ := rfl
  rw [haF]
  intro x hx
  by_cases hb : b.val < D.R.rS
  · have hfi : frame G b = G.fl.e ⟨b.val, hb⟩ := by
      have h0 := frame_castSucc G ⟨b.val, hb⟩
      rwa [show (⟨b.val, hb⟩ : Fin D.R.rS).castSucc = b from Fin.ext rfl] at h0
    rw [hfi]
    have hxe : x • G.fl.e ⟨b.val, hb⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨b.val, hb⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨b.val, hb⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hcx := (coefX_of_mem_XS D G.fl hn1).2 ⟨c.val, hc⟩
    have hd : n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨b.val, hb⟩) =
        x • (G.fl.e ⟨b.val, hb⟩ + (n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩)) := by
      rw [map_smul]; congr 1; abel
    have hne : (⟨b.val, hb⟩ : Fin D.R.rS) ≠ ⟨c.val, hc⟩ := by
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e, if_neg hne,
      zero_add] at hcx
    exact hcx
  · have hfz : frame G b = G.fl.z := by
      have h0 := frame_last G
      rwa [show Fin.last D.R.rS = b from Fin.ext (by have := b.isLt; simp; omega)] at h0
    rw [hfz]
    have hb0 : aaF D b = 1 := by
      have : (D.R.rS : ℤ) - (b : ℕ) = 0 := by have := b.isLt; push_cast; omega
      simp only [aaF, this, neg_zero, zpow_zero]
    rw [hb0] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hcx := (coefX_of_mem_XS D G.fl hv).2 ⟨c.val, hc⟩
    rw [← Algebra.smul_def]
    exact fi_smul _ o hcx

end Glob

end Formalism.L2.SG.Pf.FibQ
