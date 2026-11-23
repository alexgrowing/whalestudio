import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RootDiscriminantDegreeRatioLeRootDiscriminantSq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedValuationBoundAlgebraicPointsStatement

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem PageOK.runNum {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {X : PJ D B P j}
    {H : KHyp} {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.PtTie.RunNum D wL (cc D large₂ C2 A2 7 wL) ∧ 0 < cc D large₂ C2 A2 7 wL := by
  obtain ⟨hA, hS, h3, -, -⟩ := hP.hyp
  constructor
  · let n : ℕ := (D.host.g 0 * D.host.g 1) ^ DF wL
    refine GlobalTheory.PtTie.runNum_of_sizes D large₂ B P j hj X H C2 A2 7 ⟨(n : 𝓞 B.KO), 0, 0, 0⟩ ka wL wF Tn nP nW h0 hA hS h3
      ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩ (by norm_num)
    have e : σ ((n : 𝓞 B.KO) : B.KO) = (n : ℂ) := by
      rw [show ((n : 𝓞 B.KO) : B.KO) = (n : B.KO) from map_natCast (algebraMap (𝓞 B.KO) B.KO) n, map_natCast]
    show _ ≤ Real.log ‖σ ((n : 𝓞 B.KO) : B.KO)‖
    rw [e, Complex.norm_natCast]
    have e2 : Real.log (n : ℝ) = (DF wL : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
      simp only [n]
      push_cast
      rw [Real.log_pow]
    have p : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
      rw [← Nat.cast_mul]
      exact Real.log_natCast_nonneg _
    have p' : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    rw [e2]
    nlinarith [mul_nonneg p' p]
  · have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
    have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    have hm : 0 < D.R.m := hj.1.trans hj.2
    have hs : (0 : ℝ) < 2 * (D.R.f : ℝ) * D.R.m := by positivity
    have hR : 0 < WeightFamilies.RRv D 7 := Real.rpow_pos_of_pos (hs.trans_le hrd) _
    have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * nW + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hP.p13
    have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := lt_of_lt_of_le (by positivity) h5
    have hD : 0 < DF wL := lt_of_lt_of_le (by norm_num) hP.df
    have hq := modulus_pos_of_third_hypothesis h3
    unfold cc
    positivity

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem combBound_run : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → CombBound G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) (nusR h j wL) ∧ 0 < (cc D large₂ C2 A2 7 wL) := by
  intro hH D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hO hP G hG
  obtain ⟨hR, hc⟩ := hP.runNum hj
  exact ⟨GlobalTheory.T.combinedValuationBound_algebraicPoints hH D T h j hj hinj EX wL _ hO hR ka wF _ G rfl (fun hm => ⟨(hG hm).1, (hG hm).2.2.1⟩), hc⟩

end GlobalTheory.RunJoin
