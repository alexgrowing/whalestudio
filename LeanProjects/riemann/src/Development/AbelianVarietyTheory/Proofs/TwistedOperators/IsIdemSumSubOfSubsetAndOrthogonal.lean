import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.IdemSubDiff

variable {D : D7} [DecidableEq (Pl D.host.E)]

theorem comp_sum {es : Pl D.host.E → AE D} {S : Finset (Pl D.host.E)}
    (h : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) :
    infPart D (∑ PP ∈ S, es PP) = 0 ∧
      ∀ w, cpt (D := D) w (toEAf D (∑ PP ∈ S, es PP)) = if w ∈ S then 1 else 0 := by
  refine ⟨?_, fun w => ?_⟩
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) (h Q hQ)).1
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum, GlobalTheory.FunObj.Comparison₂.hom_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
      exact (cpt_of_isIdemAt (h w hw)).1
    · exact Finset.sum_eq_zero fun Q hQ => (cpt_of_isIdemAt (h Q hQ)).2 w fun h' => hw (h' ▸ hQ)

theorem isIdemSum_sdiff : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)},
    IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  intro D _ e e₀ P P₀ h h0 hsub
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  obtain ⟨i0, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h0
  obtain ⟨j0, d⟩ := comp_sum hes
  rw [← he] at j0 d
  have hes0 : ∀ PP ∈ P₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP := fun PP hPP => hes PP (hsub hPP)
  obtain ⟨k0, k⟩ := comp_sum hes0
  have he0 : e₀ = ∑ PP ∈ P₀, es PP := by
    refine GlobalTheory.FunObj.ae_ext (by rw [i0, k0]) fun w => ?_
    rw [k w]
    split_ifs with hw
    · exact c1 w hw
    · exact c0 w hw
  have hdiff : e - e₀ = ∑ PP ∈ P \ P₀, es PP := by
    rw [he, he0, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hmul : e * (e - e₀) = e - e₀ := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, d w]
    by_cases hw : w ∈ P
    · rw [if_pos hw, one_mul]
    · have hw0 : w ∉ P₀ := fun h' => hw (hsub h')
      rw [if_neg hw, c0 w hw0, zero_mul, sub_zero]
  have horth : e₀ * (e - e₀) = 0 := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero, RingHom.map_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_zero, d w]
    by_cases hw0 : w ∈ P₀
    · rw [c1 w hw0, if_pos (hsub hw0), sub_self, mul_zero]
    · rw [c0 w hw0, zero_mul]
  refine ⟨⟨⟨es, fun PP hPP => hes PP (Finset.mem_sdiff.1 hPP).1, hdiff⟩, ?_⟩, horth⟩
  have h1 : (e - e₀) * cA D (e - e₀) = ((e - e₀) * cA D (e - e₀)) * (e * cA D e) := by
    conv_lhs => rw [← hmul]
    rw [map_mul]
    ring
  rw [h1, hc, mul_zero]

end GlobalTheory.IdemSubDiff
