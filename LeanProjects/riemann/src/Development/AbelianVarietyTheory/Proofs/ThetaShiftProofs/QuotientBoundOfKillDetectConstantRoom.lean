import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf
import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspForStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem room_of_bounds {z k Ch Ah C₀ A₀ Cd Ad Carch Bdeg lρ beSum : ℝ} (hz : 1 ≤ z) (hk : 0 ≤ k) (hCh : 0 ≤ Ch)
    (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (h1 : Carch ≤ C₀ * z ^ A₀ * k) (h2 : Bdeg ≤ C₀ * z ^ A₀ * k)
    (h3 : lρ ≤ Cd * z ^ Ad * k) (h4 : beSum ≤ C₀ * z ^ A₀ * k) :
    Ch * z ^ Ah * k + Carch + Bdeg + lρ / 2 ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k ∧
      beSum ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k := by
  set Ac := max Ah (max A₀ Ad)
  have hmono : ∀ A, A ≤ Ac → z ^ A ≤ z ^ Ac := fun A hA => Real.rpow_le_rpow_of_exponent_le hz hA
  have hAh : z ^ Ah ≤ z ^ Ac := hmono _ (le_max_left _ _)
  have hA₀ : z ^ A₀ ≤ z ^ Ac := hmono _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hAd : z ^ Ad ≤ z ^ Ac := hmono _ (le_trans (le_max_right _ _) (le_max_right _ _))
  have hzA : 0 ≤ z ^ Ac := Real.rpow_nonneg (by linarith) _
  have e0 : Ch * z ^ Ah * k ≤ Ch * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAh hCh) hk
  have e1 : C₀ * z ^ A₀ * k ≤ C₀ * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA₀ hC₀) hk
  have e2 : Cd * z ^ Ad * k ≤ Cd * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAd hCd) hk
  have p0 : 0 ≤ Ch * z ^ Ac * k := mul_nonneg (mul_nonneg hCh hzA) hk
  have p1 : 0 ≤ C₀ * z ^ Ac * k := mul_nonneg (mul_nonneg hC₀ hzA) hk
  have p2 : 0 ≤ Cd * z ^ Ac * k := mul_nonneg (mul_nonneg hCd hzA) hk
  have e : (Ch + 3 * C₀ + Cd) * z ^ Ac * k = Ch * z ^ Ac * k + 3 * (C₀ * z ^ Ac * k) + Cd * z ^ Ac * k := by ring
  rw [e]
  constructor <;> linarith

theorem log₂ {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka)) :
    Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) ≤ Real.log (Module.finrank B.KO (B.Cusp j ka) : ℝ) := by
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg hlat.span_eq_top (WeightFamilies.MggK B CR Tt cc j ka)
  rcases Nat.eq_zero_or_pos (WeightFamilies.rhoP B CR Tt cc j ka) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (hrk ▸ Nat.le_add_right _ _))

theorem qat_of_kill_detect : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D) (Ck Ch Ah C₀ A₀ Cd Ad : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka → KillQ h j ka CR Tt cc → DetectQ h j ka CR Tt cc → 1 ≤ zBase large₂ → 0 ≤ C₀ → 0 ≤ Cd → RoomAt large₂ j ka CR Tt cc C₀ A₀ → Real.log (Module.finrank T.Q.c.F ((recB h).Cusp j ka) : ℝ) ≤ WeightFamilies.PPv D large₂ Cd Ad * ka.size → Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
  intro hK D T h j ka CR Tt cc large₂ Ck Ch Ah C₀ A₀ Cd Ad hG hj hjm hlat hkill hdet hz hC₀ hCd hroom hdim
  intro hCR hOb hn hlast hsize hT hc hTc
  have hzpos : 0 < zBase large₂ := by linarith
  have hCh : 0 ≤ Ch := by
    have h1 : (1 : ℝ) ≤ WeightFamilies.degO (recB h) := by
      unfold WeightFamilies.degO
      exact_mod_cast Module.finrank_pos
    have h2 : 0 ≤ Ch * zBase large₂ ^ Ah := (Real.log_nonneg h1).trans hOb.1
    exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos hzpos _)
  have hA : (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) ≤ ka.size := by
    have h1 := absA_add_le_size T h.pins hj ka
    have h2 : (0 : ℝ) ≤ (fdeg D.host.E : ℝ) * ka.n := by positivity
    linarith
  have hk : (0 : ℝ) ≤ ka.size := (Nat.cast_nonneg _).trans hA
  have hnpos : 0 < nAt D j ka CR Tt cc := Nat.succ_pos _
  obtain ⟨hfin, hsum⟩ := beSum_holds D.host.E (recB h).KO (nAt D j ka CR Tt cc)
    (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)) hnpos
  have hP₀ : 0 ≤ C₀ * zBase large₂ ^ A₀ := mul_nonneg hC₀ (Real.rpow_pos_of_pos hzpos _).le
  have hsum' := hsum.trans ((mul_le_mul_of_nonneg_right hroom.2.2 (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hA hP₀))
  have hlog := log₂ (recB h) j ka CR Tt cc hlat
  obtain ⟨hr1, hr2⟩ := room_of_bounds (Ah := Ah) hz hk hCh hC₀ hCd hroom.1 hroom.2.1 (hlog.trans hdim) hsum'
  refine qat_of_bridge' large₂ (recB h) j ka CR Ck Ch Ah _ _ Tt cc hlat
    (qbridge_of_numGood D large₂ (recB h) j ka CR Ch Ah _ _ Tt cc
      (beOf D.host.E (nAt D j ka CR Tt cc) (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)))
      (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) hlat (fun la => ?_) hfin hr2
      (recB_supN_conj h j ka) hr1 fun F hF => ?_) hCR hOb hn hlast hsize hT hc hTc
  · unfold beOf
    positivity
  · by_contra hno
    refine hF (hdet F fun K₁ i1 i2 i3 d hd => ?_)
    by_contra hne
    obtain ⟨φ, hφ, hgood⟩ := GlobalTheory.T.cmArcDatumFamily_functional_bounded_linear_on_cuspForms hK D T h j ka CR Tt cc large₂ hG hj hjm K₁ d hd
    refine hno ⟨K₁, i1, i2, i3, φ, fun G hGm => ?_, ?_, hgood⟩
    · exact (hφ G).trans (hkill K₁ d hd G hGm)
    · exact fun h0 => hne ((hφ F).symm.trans h0)

end GlobalTheory.ArcCM
