import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

noncomputable section

namespace GlobalTheory.DepthBoundProbe

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem choose_two_add (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem dimY_eq (Tp : ParamsT D L P) {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = Tp.Dp := by
  rw [Tp.Dp_eq]
  unfold WeightFamilies.dimY
  congr 1
  have hr : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [hr, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]

theorem kappa_last (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    2 * (Tp.TO : ℤ) ^ 2 ≤ ((kaR Tp hK j).aP τ i : ℤ) := by
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hc := P.e_centred τ ⟨j - 1, by omega⟩
  have h0 := Tp.heightBound_ge_order_sq
  have hi1 : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)
  have hcast : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : i.1 + 2 = D.R.k + j := by omega
    have : ((i.1 : ℕ) : ℚ) + 2 = (D.R.k : ℚ) + j := by exact_mod_cast this
    linarith
  rw [DV.aPlusQ_eq, hcast] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hi1, dif_pos hb, dif_pos ⟨h1, h2⟩, hidx] at e2
  have ht : 5 ≤ D.R.t := by
    have a1 := Tp.split; have a2 := Tp.nP_eq; have a3 := Tp.TO_nW; have a4 := Tp.nW_40
    have : 1 * Tp.nWn ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_right _ (by have := Tp.TO_40; omega)
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ a4
    omega
  have ht' : (5 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have e3 : ((D.what₂.kaBig j τ i : ℤ) : ℝ) =
      ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this ⊢
    linarith
  have h4 := (abs_le.1 hc).1
  have : (2 * (Tp.TO : ℝ) ^ 2) ≤ ((D.what₂.kaBig j τ i : ℤ) : ℝ) := by rw [e3]; linarith
  unfold kaR
  rw [e1]
  exact_mod_cast this

theorem lR_lastPos (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (lR Tp hK j).LastPos := by
  intro τ i hi
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := kappa_last Tp hK hj τ i hi
  show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (1 : ℤ) ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) / (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [dimY_eq Tp hj]
    push_cast
    nlinarith
  omega

theorem one_le_DF (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    1 ≤ WeightAlgebra.DF (lR Tp hK j) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_lastPos Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (le_trans h1 (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _))) (Nat.le_add_right _ _)

end GlobalTheory.DepthBoundProbe
