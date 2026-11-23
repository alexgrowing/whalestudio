import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def signEquiv {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem signEquiv_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (signEquiv ε (Sum.inl i)) = true := by
  have h := ((Fintype.equivFin {a // ε a = true}).symm i).2
  simpa [signEquiv] using h

theorem signEquiv_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (signEquiv ε (Sum.inr j)) = false := by
  have h := ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2
  simpa [signEquiv] using h

theorem muCD_eq_smul (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hc : Formalism.MainNotions.RT.cdScaleTieR cd s) {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (s N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (signEquiv ε) (signEquiv_inl ε) (signEquiv_inr ε) A hA,
    hc N ε _ _ (signEquiv ε) (signEquiv_inl ε) (signEquiv_inr ε) A hA]

theorem card_add_card {N : ℕ} (ε : Fin N → Bool) :
    (Finset.univ.filter (fun a => ε a = true)).card + (Finset.univ.filter (fun a => ε a = false)).card = N := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ a : Fin N, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h1]
  simp

theorem thrStar_lt {N : ℕ} (ε : Fin N → Bool) (hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε)
    (hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε) {h : ℝ}
    (hh : 32 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 2 < h) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by
  have hpN : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ N := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hpR : (1 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) := by exact_mod_cast hp
  have hqR : (1 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by exact_mod_cast hq
  have hN : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hpR hN
  have hm : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε * ReciprocityTheory.ChartRestriction.DS.qOf ε := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0
      exact le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by
    have : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0
      exact le_min hp hq
    exact_mod_cast this
  have h2m : (0 : ℝ) ≤ 2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by positivity
  have hsq : Real.sqrt (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)) ≤ 2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt h2m, Real.sqrt_nonneg (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)),
      sq_nonneg (Real.sqrt (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)) - 1)]
  have hA : (N : ℝ) * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) ≤
      (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hB : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤
      (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hN1
  have hC : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  rw [← lt_sub_iff_add_lt, max_lt_iff]
  constructor <;> linarith

theorem fdeg_cd_gap {n : ℕ} {ε : Fin n → Bool} (hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε)
    (hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε) {lam : Fin n → ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ v = ReciprocityTheory.ChartRestriction.DS.dimVlam lam := by
  have : CompleteSpace H := hσ.1
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have h1 := le_max_right
      ((n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1)
      (16 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)))
    have h2 : 0 ≤ 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := by positivity
    have h3 : 0 ≤ (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    unfold ReciprocityTheory.ChartRestriction.DS.thrStar at hh
    linarith
  have hΨ : ∀ μ : Fin n → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  exact ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp hq hlam hgap hh hΨ hσ hv

theorem hCFdegRGap_holds : HCFdegRGap := by
  intro cd s hc N ε lam h hp hq hlam hgap hh H _ _ σ w hσ hw
  rw [← muCD_eq_smul cd s hc ε]
  exact fdeg_cd_gap hp hq hlam hgap (thrStar_lt ε hp hq hh) hσ hw

end PI.UnitaryGroupMassFormula.HCFdegRGap
