import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairNormNeZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPeterssonNormEqRallisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairNormNeZeroStatement

section
noncomputable section
open NumberField
open GlobalTheory.SqTop
namespace GlobalTheory.NormBigNe
theorem big_theta_petersson_norm_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  rintro hP hI ⟨a, k⟩
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨c, x, l⟩ := k ε CF hCF
  refine ⟨c, x, fun C hC D large₂ he hx hR T Lc μ₀ hμ G δ t0 i j t Q P P' hb => ?_⟩
  obtain ⟨Λ, hΛ, hne⟩ := (l C hC D large₂ he hx hR T Lc μ₀ hμ G i j).1 t
  have e := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hμ G hb hΛ
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  intro h0
  rw [h0, Complex.ofReal_zero] at e
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
  · unfold GlobalTheory.NormRatio.normFactor
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.fockSum_ne_zero D _ _ _ P.a_le)) ?_) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
    · exact_mod_cast (GlobalTheory.NormExact.normConst_pos P.crv _ _).ne'
    · exact_mod_cast GlobalTheory.VacuumNorm.vacNorm_ne_zero D ⊤ δ t0 P.crv P.pt0 _ _
  · obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    exact hne s hs1 (hs2.trans (by exact_mod_cast GlobalTheory.SqTop.squareBottomHalfRankSum_le_halfRank D i j))
end GlobalTheory.NormBigNe
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  first | exact @_root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | exact _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | (intros; apply _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero <;> assumption)
end
