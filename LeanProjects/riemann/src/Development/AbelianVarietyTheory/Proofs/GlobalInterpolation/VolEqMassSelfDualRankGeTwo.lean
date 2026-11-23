import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianSpaceSelfDualLatticeSignatureStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioUpPositiveLineStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_step (D : D7) (hT : VolTie D) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D)
    (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hPQ : 2 ≤ P + Q)
    (hup : ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U = massI D (P + Q + 1)) :
    D.vol W = massI D (P + Q) := by
  obtain ⟨U, hU, hUs⟩ := GlobalTheory.T.exists_hermitianSpace_with_signature D (P + 1) Q
  have hr := GlobalTheory.T.volume_ratio_up_positive_line D hT h2 W P Q hW hs hPQ U hU hUs
  have hb := massRatio_of_definiteVolume D h2 hv (P + Q + 1) (by omega)
  have e : P + Q + 1 - 1 = P + Q := by omega
  rw [e] at hb
  rw [← hb, hup U hU hUs] at hr
  have h1 := massI_pos D (P + Q + 1)
  have h3 := massI_pos D (P + Q)
  have h4 := D.vol_pos W
  field_simp at hr
  nlinarith [hr]

theorem vol_eq_massI_of_two_le_rank : ∀ D : D7, VolTie D → Conclusion2 D → DefiniteVolumeEqMass D → ∀ (W : HSpace D.host.E) (P Q : ℕ),
    W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → D.vol W = massI D (P + Q) := by
  intro D hT h2 hv
  have h2v := volume_eq_mass_of_definite D h2 hv
  have hP1 : ∀ (W : HSpace D.host.E) (Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (1, Q)) → 2 ≤ 1 + Q →
      D.vol W = massI D (1 + Q) := by
    intro W Q hW hs hQ
    refine vol_eq_massI_step D hT h2 hv W 1 Q hW hs hQ fun U hU hUs => ?_
    have := h2v.2 U 2 Q hU hUs le_rfl
    rw [this]; congr 1; omega
  intro W P Q hW hs hPQ
  rcases Nat.lt_or_ge P 2 with hP | hP
  · interval_cases P
    · refine vol_eq_massI_step D hT h2 hv W 0 Q hW hs hPQ fun U hU hUs => ?_
      rw [hP1 U Q hU hUs (by omega)]; congr 1; omega
    · exact hP1 W Q hW hs hPQ
  · exact h2v.2 W P Q hW hs hP

end GlobalTheory.Glob
