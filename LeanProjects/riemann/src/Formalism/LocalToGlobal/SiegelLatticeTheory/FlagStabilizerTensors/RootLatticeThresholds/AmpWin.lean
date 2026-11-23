import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocNorm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.AmpWin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def kap (τ : D.what₂.Tau) : ℝ := Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)

def AmpWinP : Prop :=
  (∏ τ, kap u u' C hB τ) * c0X X u (Y.FN u) * c0X X u' (Y.FN u') =
    X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')

def MassU : Prop :=
  (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal =
    Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal

end Defs

section Lemmas

variable {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C)

theorem cOf_pos {u : D.what₂.Word} {τ : D.what₂.Tau} (h0 : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0)
    (ht : l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤) : 0 < cOf hB u τ := by
  have hl : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos h0 ht.ne
  have hd : 0 < Module.finrank ℂ (X.Vloc u (vOf X τ)) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (X.Vloc u (vOf X τ))) with h | h
    · exfalso
      have : Subsingleton (X.Vloc u (vOf X τ)) := Module.finrank_zero_iff.1 h
      apply h0
      unfold l2SG
      simp [Subsingleton.elim (phiOf hB u τ _) 0]
    · exact h
  unfold cOf
  exact div_pos hl (by exact_mod_cast hd)

theorem kap_eq {u u' : D.what₂.Word} {τ : D.what₂.Tau} (hc : 0 < cOf hB u τ) (hc' : 0 < cOf hB u' τ) :
    kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := by
  unfold kap Formalism.L2.SG.Pf.LocNorm.aT sclOf
  have hb : cOf hB u' τ = (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal / ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := rfl
  have hd0 : (0 : ℝ) ≤ ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hb] at hc' ⊢
  generalize cOf hB u τ = a at hc ⊢
  generalize (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal = L at hc' ⊢
  generalize ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) = d at hd0 hc' ⊢
  have hd : 0 < d := lt_of_le_of_ne hd0 (fun h => by rw [← h, div_zero] at hc'; exact lt_irrefl _ hc')
  have hL : 0 < L := by
    have h1 := mul_pos hc' hd
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  have hx : 0 ≤ a * d / L := div_nonneg (mul_nonneg hc.le hd.le) hL.le
  first
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (simp only [Complex.normSq_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp)

theorem finrank_tau (u : D.what₂.Word) :
    (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact (Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl).symm

end Lemmas

section Main

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

theorem poincareConstant_of_mass (hM : MassU Y u C hB) :
    c0X X u (Y.FN u) = X.volK2 * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, cOf hB u τ := by
  unfold c0X
  unfold MassU at hM
  rw [mul_assoc X.volK2, hM, finrank_tau u]
  have hP : ∏ τ, cOf hB u τ = (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) / ∏ τ, ((Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℕ) : ℝ) := by
    rw [← Finset.prod_div_distrib]
    rfl
  rw [hP]
  ring

theorem ampWin_of (hM : MassU Y u C hB) (hM' : MassU Y u' C hB)
    (hl : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hl' : ∀ τ, l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤) :
    AmpWinP Y u u' C hB := by
  unfold AmpWinP
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => cOf_pos hB (hl τ).1 (hl τ).2
  have hc' : ∀ τ, 0 < cOf hB u' τ := fun τ => cOf_pos hB (hl' τ).1 (hl' τ).2
  have hk : ∀ τ, kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := fun τ => kap_eq hB (hc τ) (hc' τ)
  have hP : (∏ τ, kap u u' C hB τ) * (∏ τ, cOf hB u τ) * (∏ τ, cOf hB u' τ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    have h1 := (hc τ).ne'
    have h2 := (hc' τ).ne'
    rw [hk τ]
    field_simp
  rw [poincareConstant_of_mass _ _ _ _ hM, poincareConstant_of_mass _ _ _ _ hM']
  linear_combination (X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')) * hP

theorem poincareConstant_nonneg (w : D.what₂.Word) : 0 ≤ c0X X w (Y.FN w) := by
  unfold c0X
  first
    | positivity
    | (have := X.levelVolume_pos; positivity)
    | (have := X.volK2_nonneg; positivity)
    | (unfold HidaSetting.volK2; positivity)
    | (unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2; done)

theorem K0_eq_covN_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) :
    Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB =
      Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' := by
  have ha := poincareConstant_nonneg Y u
  have hb := poincareConstant_nonneg Y u'
  unfold Formalism.L2.SG.Pf.LocNorm.K0 Formalism.L2.SG.Pf.OOCore3.sclV TermOp.scl
  unfold AmpWinP at hA
  have hkap : ∀ τ, kap u u' C hB τ = Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ) := fun τ => rfl
  simp only [hkap] at hA
  generalize (∏ τ, Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)) = P at hA ⊢
  generalize c0X X u (Y.FN u) = a at ha hA ⊢
  generalize c0X X u' (Y.FN u') = b at hb hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u = m at hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' = m' at hA ⊢
  generalize X.volK2 = V at hA hV ⊢
  clear hkap
  rw [Complex.normSq_ofReal]
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | h0
  · rw [← h0, Real.sqrt_zero, inv_zero, zero_mul, mul_zero, div_zero]
    have h1 : V ^ 2 * (m * m') = 0 := by rw [← hA, mul_assoc, ← h0, mul_zero]
    exact ((mul_eq_zero.mp h1).resolve_left (pow_pos hV 2).ne').symm
  · have hs : (√(a * b)) ^ 2 = a * b := Real.sq_sqrt h0.le
    have hs0 : √(a * b) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have hden : (√(a * b))⁻¹ * V * ((√(a * b))⁻¹ * V) = V ^ 2 / (a * b) := by
      first
        | rw [inv_mul_eq_div, div_mul_div_comm, ← sq, ← sq, hs]
        | (field_simp; rw [hs]; ring)
        | (field_simp; rw [Real.mul_self_sqrt h0.le]; ring)
    rw [hden, div_div_eq_mul_div, div_eq_iff (pow_pos hV 2).ne']
    linarith [hA]

theorem minWeight_pos (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  exact hc

theorem K0_mem_covWin_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  first
    | exact hW
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; exact hW)
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; done)

end Main

end Formalism.L2.SG.Pf.AmpWin
