import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoAndShareRhoTOfShareRhoR
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinalJoin

theorem inputs4_of_inputsR : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P X j h1 h2 large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus hI hTC hPA hPS
  obtain ⟨⟨hH, hLat, hLAM, hQ, hSub⟩, hSup, hHerm, G, Gc, PH, Prw, Pet, Pd, hLogD,
    ⟨hW, hTh, hEt, hPGd, hPG4, hPGq, hRd, hRho, hRhoP, hPoly, hB, hM⟩, hComb, Qf, hC, hTie, hLift, hHt⟩ := hI
  have hSet := hH.2.1
  have hH2 := hH.2.2.2.2.1
  obtain ⟨hS0, hSK⟩ := shortG_of_scalB hH.2.2.1 hPG4
  have hDT : WeightFamilies.dimY D j ≤ T := hSet.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwt : SizeBoundsAlt.wtIter wadd wL ((X j h1 h2).wF0 wL wF) (a0 D j T) = ka := by
    rw [iterated_weight_at_vanishingOrder (X j h1 h2) wL wF T hDT]; exact (ka_eq_addL_of_setC hSet).symm
  obtain ⟨rz, alz, th0, zc, hTZ, hZ⟩ := exists_global_family_zero_choice G S T Gc hwt hS0 hH2.2.2.1
  obtain ⟨th, hTQ⟩ := exists_global_family_quotient_bounded
    ({ G with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData (X j h1 h2) ka wL wF) large₂ S K.CRm T
    (cc D large₂ C2 A2 CR wL) (Gc * ka.size) Ch Ah hSK hH2.2.2.2
    (mul_le_mul_of_nonneg_right hPGq (by linarith [ka.one_le_size]))
  obtain ⟨hR1, hR2⟩ := GlobalTheory.shareRho_and_shareRhoT_of_shareRhoR D B P j (X j h1 h2) ka wL wF
    (G.setZQ rz alz th0 zc _ th) S T _ Gc hRho hTZ hZ
  have hM' : ∀ la, InContainM (G.setZQ rz alz th0 zc _ th) la K.CRm T (cc D large₂ C2 A2 CR wL) :=
    fun la => inContainM_of _ la S _ T _ (hM la) (hZ la)
  have hLift' : ∀ la, ((Qf la).tr G rz alz th0 zc _ th).InLiftC S Gc Prw T :=
    fun la => tr_InLiftC G rz alz th0 zc _ th (Qf la) S Gc Prw T (hLift la)
  refine ⟨hH, hLat, hSup, hLAM, hQ, hTC, hPA, hPS, G.setZQ rz alz th0 zc _ th, Gc, PH, Prw, Pet, Pd,
    hW, hTh, hTZ, hTQ, hEt, hHerm, hSub, hLogD, pageGd4_iff.mpr hPGd, hRd, hR2, hRhoP, polyDom4_iff.mpr hPoly, hZ, hM',
    fun hj => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift',
      combBound4_of hj (tr_CombBound G rz alz th0 zc _ th S _ nus hComb) _, hHt⟩,
    fun hj => depthAtM_of hj hComb, fun _ _ => ?_,
    fun _ => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift', hHt⟩⟩
  exact theorem_zero_of_named_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH hLat hSup hLAM hQ
    (G.setZQ rz alz th0 zc _ th) Gc PH Prw Pet Pd (fun la => (Qf la).tr G rz alz th0 zc _ th)
    hW hTh hTZ hTQ hEt hHerm hSub hLogD hPGd hRd hR1 hRhoP hPoly hB hC hTie hLift' hZ hM' hComb hHt

end GlobalTheory.FinalJoin
