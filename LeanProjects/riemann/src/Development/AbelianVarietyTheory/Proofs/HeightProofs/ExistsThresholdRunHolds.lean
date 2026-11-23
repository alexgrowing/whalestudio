import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundChosenFamilyOfIntrinsicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundIntrinsicHypothesesNetBoundDegreeTwoStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIndexBoundHypothesesWithNetAllValuedPointsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThresholStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem scalOfP_base {D : D7} {B : WeightFamilies.Prov D} (n : SecNorm B) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p : ℕ) {j : ℕ} (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ) :
    scalOfP n.base hinj EX p ka wL wF Tn = scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 (scalOfP B hinj EX p ka wL wF Tn) := rfl

set_option maxHeartbeats 4000000 in

theorem indexBoundConclusion_secondNorm_iff {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ) :
    Concl (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nus
      ((PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X).rk ka (n.base.Mlat j ka) * a * b * c * d) ↔
    Concl X S ka wL wF Tn nus (X.rk ka (B.Mlat j ka) * a * b * c * d) := Iff.rfl

set_option maxHeartbeats 4000000 in

theorem inputs4_of_net {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Cq C2 A2 CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hn : InputsNet large₂ (X j h1 h2) (kR CL) H 1 4 Cq 4 C2 A2 7 CT S ka wL wF Tn nP nW h0 nus)
    (ht : H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ 12 ≤ A2) (hp : PageAt large₂ C2 A2)
    (hs : PageSupp D large₂ B C2 A2 nW S wL) :
    ∃ n : SecNorm B,
      Inputs4 large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)) (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT
        (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus ∧
      Concl (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nus
        ((PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)).rk ka (n.base.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b *
          large₂.de2) := by
  obtain ⟨n, hR⟩ := GlobalTheory.T.exists_secNorm_inputsR_of_inputsNet D B P j (X j h1 h2) large₂ (kR CL) H 1 4 Cq 4 C2 A2 7 CT S ka wL wF Tn nP nW h0 nus hn
  have hR' := GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo D _ P j _ large₂ CL H 1 4 Cq 4 C2 A2 7 CT _ ka wL wF Tn nP nW h0 _ hR
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := ht
  have hT : TieC (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, by norm_num [k4], le_rfl, le_rfl, by norm_num⟩
  let Y : WeightAlgebra.Prov D n.base P := fun j h1 h2 => PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)
  have h4 := GlobalTheory.T.indexBoundChosenFamily_of_intrinsicHypotheses D n.base P Y j h1 h2 large₂ (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT
    (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus hR' hT hp hs
  exact ⟨n, h4, concl_of_inputs4 large₂ Y (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT j h1 h2 _ ka wL wF Tn nP nW h0 nus h4⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem runHolds_of_parOK : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → RunHolds x₀ h hinj EX p := by
  obtain ⟨CL, Cq, Z₀, hrec⟩ := GlobalTheory.T.exists_indexBoundHypothesesWithNet_allValuedPoints
  obtain ⟨x₀, hx⟩ := GlobalTheory.T.runNumericalConditions_of_indexBound_beyond_threshold Z₀
  refine ⟨x₀, fun D T h hinj EX p hpar j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hrun hx0 => ?_⟩
  obtain ⟨hok, hZ⟩ := hx D _ _ j _ large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hrun hx0
  obtain ⟨hn, hs⟩ := hrec D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 (hpar j hj) hok hZ
  obtain ⟨n, h4, hc⟩ := inputs4_of_net (fun j h1 h2 => recPlus h j ⟨h1, h2⟩) j hj.1 hj.2 large₂ CL H (Cq H.CA H.CK) C2 A2 CT
    _ ka wL wF Tn nP nW h0 _ hn hrun.tie hrun.page hs
  refine ⟨⟨n, k4 large₂ CL, Cq H.CA H.CK, ?_, ?_⟩, ?_, ?_⟩
  · rw [scalOfP_base]; exact h4
  · rw [scalOfP_base]; exact hc
  · exact (hypC_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) large₂ H C2 A2 7 0 CT _ Tn nP nW h0 _).1 hn.1.1
  · exact (concl_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) _ ka wL wF Tn _ _).1
      ((indexBoundConclusion_secondNorm_iff n _ _ ka wL wF Tn _ _ _ _ _).1 hc)

end GlobalTheory.FinalJoin
