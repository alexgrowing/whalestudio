import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace GlobalTheory.TopDegLower

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem lR_last_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    Tp.TO ≤ (lR Tp hK j).aP τ i + 1 := by
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := GlobalTheory.DepthBoundProbe.kappa_last Tp hK hj τ i hi
  show Tp.TO ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i + 1
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (Tp.TO : ℤ) - 1 ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) /
      (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
    push_cast
    have hD : (0 : ℤ) ≤ Tp.Dp := Int.natCast_nonneg _
    have h2 : ((Tp.TO : ℤ) - 1) * ((Tp.Dp : ℤ) + 2) ≤ ((Tp.TO : ℤ) - 1) * Tp.TO :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  omega

theorem DF_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    Tp.TO ≤ WeightAlgebra.DF (lR Tp hK j) + 1 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_last_ge Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine h1.trans (Nat.add_le_add_right ?_ 1)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _)) (Nat.le_add_right _ _)

theorem two_pi_nW_le_topDeg_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D),
    2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  intro D L Pm Tp hK
  have hj : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨τ, -⟩ := GlobalTheory.FinalJoin.RecordRun.exists_thick L
  have h1 := DF_ge Tp hK hj τ
  have h2 : WeightAlgebra.DF (lR Tp hK 1) ≤ GlobalTheory.IndexAssembly.topDeg Tp hK := GlobalTheory.IndexAssembly.le_topDeg Tp hK hj
  have h3 : 2 * Tp.nWn ≤ Tp.TO := by
    have := Tp.TO_nW
    nlinarith [Nat.zero_le (Tp.Dp * Tp.nWn)]
  have h4 : 40 ≤ Tp.TO := by have := Tp.TO_40; omega
  have a : (Tp.TO : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) + 1 := by
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 1)
  have b : 2 * (Tp.nWn : ℝ) ≤ Tp.TO := by exact_mod_cast h3
  have c : (40 : ℝ) ≤ Tp.TO := by exact_mod_cast h4
  have hpi := Real.pi_le_four
  have hn : (0 : ℝ) ≤ Tp.nWn := Nat.cast_nonneg _
  have d : 2 * Real.pi * (Tp.nWn : ℝ) ≤ 4 * Tp.TO := by nlinarith
  nlinarith

end GlobalTheory.TopDegLower
