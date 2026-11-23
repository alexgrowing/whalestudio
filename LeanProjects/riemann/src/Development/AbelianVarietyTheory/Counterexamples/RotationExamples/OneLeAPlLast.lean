import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.ThetaFiresProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem labE_fixed (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem lab_fixed (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_fixed ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [labE_fixed] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 := by
      exact AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem one_le_aPl_last (i : Fin D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aPl D i (D.R.k + i) τ (D.R.k + i - 1) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  unfold aPl Formalism.L2.NTheta.lamAt
  rw [if_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
  have e : (⟨D.R.k + i - 1 - (D.R.k - 1), by omega⟩ : Fin D.R.m) = i := Fin.ext (by simp; omega)
  rw [e]
  have g := (D.hc τ).gap_be i
  have c : ((D.R.k + i - 1 : ℕ) : ℚ) = (D.R.k : ℚ) + i - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [c, Int.le_toNat (Int.floor_nonneg.2 (by push_cast; linarith)), Int.le_floor]
  push_cast; linarith

theorem parAt_fixed (W : HSp D) (ρ : D.what₂.Tau) :
    parAt W D.what₂.embLL ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D W ρ) := by
  unfold parAt kapAt
  rw [lab_fixed, if_pos (labE_fixed ρ)]
  rfl

end GlobalTheory.ThetaFiresProbe
end
