import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.FdegUniqG
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesExistence.ExistsG
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.OwnFacts.FD

variable {D : D7}

theorem cdScale_eq_muCD (hT : Ties D) :
    ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) = ReciprocityTheory.ChartRestriction.DS.muCD (epsSH D.R) := by
  ext A hA
  rw [hT.cdScale_tie _ (epsSH D.R) _ _ (Formalism.BasicNotions.Examples₂.CD.e0 (epsSH D.R)) (Formalism.BasicNotions.Examples₂.CD.sign_split_equiv_inl (epsSH D.R))
    (Formalism.BasicNotions.Examples₂.CD.sign_split_equiv_inr (epsSH D.R)) A hA]
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol D.cd (Formalism.BasicNotions.Examples₂.CD.e0 (epsSH D.R)) (Formalism.BasicNotions.Examples₂.CD.sign_split_equiv_inl (epsSH D.R))
    (Formalism.BasicNotions.Examples₂.CD.sign_split_equiv_inr (epsSH D.R)) A hA]

theorem thr_lt {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    ReciprocityTheory.ChartRestriction.DS.thrStar (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have e : ReciprocityTheory.ChartRestriction.DS.thrStar (epsSH D.R) = Formalism.MainNotions.GapDS.thrE (epsSH D.R) := by
    unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS ReciprocityTheory.ChartRestriction.DS.S7.q0
    rfl
  rw [e]
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) with hnd
  have e2 : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn19 : 4 * n ^ 3 + 1 < n ^ 19 := by
    have e3 : n ^ 19 = n ^ 3 * n ^ 16 := by ring
    have e4 : (5 : ℝ) < n ^ 16 := by
      have : (6 : ℝ) ^ 16 ≤ n ^ 16 := pow_le_pow_left₀ (by norm_num) h6 16
      nlinarith
    have e5 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith)
    rw [e3]; nlinarith
  have e6 : n ^ 19 ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
  have e7 : n ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
    le_mul_of_one_le_left (by positivity) hCL
  have e8 : Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
  rw [e8]; linarith

theorem dsig_eq {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = ReciprocityTheory.ChartRestriction.DS.dimVlam (lamSH D.R (D.hc τ)) := by
  have hg := Formalism.MainNotions.BridgeLemma.szh_gap hH τ
  have hth := thr_lt hH hCL
  have hlam := Formalism.MainNotions.BridgeLemma.szh_hc hH τ
  have hpq := Formalism.MainNotions.S.Pv.DegI.minpq_pos D
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) := le_trans hpq (min_le_left _ _)
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) := le_trans hpq (min_le_right _ _)
  have hthE : Formalism.MainNotions.GapDS.thrE (epsSH D.R) < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have e : ReciprocityTheory.ChartRestriction.DS.thrStar (epsSH D.R) = Formalism.MainNotions.GapDS.thrE (epsSH D.R) := by
      unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS ReciprocityTheory.ChartRestriction.DS.S7.q0
      rfl
    linarith
  obtain ⟨H, i1, i2, σ, hσ⟩ := Formalism.MainNotions.BesselDiscreteSeries.discrete_series_exists_of_fact _ (epsSH D.R) _ hlam _ hg hthE
  have : CompleteSpace H := hσ.1
  have : Nontrivial H := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨d, hd⟩ := ReciprocityTheory.ChartRestriction.DS.fdcGood_of_isDS hσ
  have hd' : IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d := by
    rw [cdScale_eq_muCD hT]; exact hd
  have hdd : d = D.dsig τ := hT.dsig_tie τ H σ d hσ hd'
  set h : ℝ := Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L with hhdef
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) := le_min hp hq
  have h8 : 8 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) < h := by
    have h1 := le_max_right
      (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) : ℝ) *
        (ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) : ℝ) + 1)
      (16 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ) +
        8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)))
    have h2 : 0 ≤ 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)) := by positivity
    have h3 : 0 ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ) := by positivity
    have hh := hth
    unfold ReciprocityTheory.ChartRestriction.DS.thrStar at hh
    linarith
  have hΨ : ∀ μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ →
      ReciprocityTheory.ChartRestriction.DS.GapAtLeast (epsSH D.R) μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (epsSH D.R) (ReciprocityTheory.ChartRestriction.DS.lowK (epsSH D.R) μ))
        (Ψ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (T.V →L[ℂ] T.V)),
        ReciprocityTheory.ChartRestriction.DS.IsPsiFor (epsSH D.R) μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists (epsSH D.R) μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  have key := ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp hq hlam hg hth hΨ hσ hv
  rw [ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd hv] at key
  rw [← hdd, key]

instance factDsigHC : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC :=
  ⟨fun _ _ _ _ _ _ _ _ _ hT hH hCL τ => dsig_eq hT hH hCL τ⟩

end Formalism.L2.SG.OwnFacts.FD
