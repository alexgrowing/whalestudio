import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.FdegGap

def plusFirst {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem plusFirst_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (plusFirst ε (Sum.inl i)) = true := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {a // ε a = true}).symm i).2

theorem plusFirst_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (plusFirst ε (Sum.inr j)) = false := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

theorem muCD_eq_scaled (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal)
    (hc : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)})
    {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (sc N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA]
  exact (hc N ε _ _ (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA).symm

theorem one_le_p {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = true) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem one_le_q {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = false) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem thrStar_eq {N : ℕ} (ε : Fin N → Bool) : ReciprocityTheory.ChartRestriction.DS.thrStar ε = Formalism.MainNotions.GapDS.thrE ε := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS
  rfl

theorem fdeg_gap : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  intro cd sc hc N ε lam h hlam hp hq hgap hh H _ _ σ hσ
  haveI : CompleteSpace H := hσ.1
  haveI : Nontrivial H := hσ.2.1
  have hCD := muCD_eq_scaled cd sc hc ε
  have hp1 := one_le_p hp
  have hq1 := one_le_q hq
  have hh' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by rw [thrStar_eq]; exact hh
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp1 hq1
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have hm : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ ReciprocityTheory.ChartRestriction.DS.thrStar ε := le_max_right _ _
    have h0 : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hμg
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor N ε μ h T m hμ hm hμg hq0 h8).1⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdim : fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ w = ReciprocityTheory.ChartRestriction.DS.dimVlam lam :=
    ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp1 hq1 hlam hgap hh' hΨ hσ hw
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hσ
  have hpos : (0 : ℝ) < (sc N ε : ℝ) := by
    rcases (sc N ε).coe_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      haveI := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
      have hz : sc N ε = 0 := by exact_mod_cast heq.symm
      have hne := (isOpen_univ (X := Formalism.REAL.UJ ε)).measure_ne_zero (ReciprocityTheory.ChartRestriction.DS.muCD ε) Set.univ_nonempty
      rw [hCD, hz] at hne
      simp at hne
  have hsc : IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (d / (sc N ε : ℝ)) := by
    have := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hpos hd
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hval : d / (sc N ε : ℝ) = Formalism.QuantumDeterminants.fdegHC lam := by
    have h1 := ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' (hCD ▸ hsc) hw
    rw [h1] at hdim
    rw [hdim, ReciprocityTheory.ChartRestriction.DS.dimVlam_eq_vand hlam.1, Formalism.MainNotions.BridgeLemma.szh_fdegHC lam hlam.1]
    rfl
  rwa [hval] at hsc

end GlobalTheory.FdegGap
