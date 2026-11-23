import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift
variable {D : D7}

theorem U_sub_c_eq_w (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ =
      (((lamL j τ).w ⟨a, ha⟩ : ℤ) : ℝ) + ((Vc D j).rank : ℝ) / 2 - a := by
  have h1 := lamT_of_lt j τ a ha
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  show ((Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a : ℤ) : ℝ) - cT j τ = _
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN cT
  push_cast
  rw [h2]
  ring

theorem valsAt_of_isLamPrime : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  intro D L j τ h
  obtain ⟨hj, W, hk, hm, ht, hJ, he, hv, hb, hw⟩ := h
  obtain ⟨k, m, t, J, e, v, b⟩ := W
  simp only at hk hm ht hJ he hv hb
  subst hk hm ht hJ
  have hN := rank_eq j
  have hK := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hjm := j.2
  have hrk : ((Vc D j).rank : ℚ) = (D.R.k : ℚ) + D.R.m + D.R.t - 1 := by
    rw [hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hmj : ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℚ) = (D.R.m : ℚ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk1 : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr1 : D.R.k + D.R.m - 1 + D.R.t = (Vc D j).rank := by omega
  have hp : D.R.k + ((j : ℕ) + 1) - 1 = D.R.k + j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hal : a < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ a hal]
    have hq := hw ⟨a, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj] at hq
    have hv' : ((v (a + 1 + 1) : ℤ) : ℚ) = (D.hc τ).v ⟨a, ha⟩ := hv ⟨a, ha⟩
    have hQ : (((lamL j τ).w ⟨a, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - a = (D.hc τ).v ⟨a, ha⟩ := by
      rw [hq, ← hv']; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  · intro i hi
    have hal : D.R.k - 1 + i < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj, show D.R.k - 1 + (i : ℕ) + 1 - (D.R.k - 1) = (i : ℕ) + 1 by omega,
      show D.R.k - 1 + (i : ℕ) + 1 = D.R.k + i by omega] at hq
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, hk1]
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this
  · intro s hs
    have hal : D.R.k + j + s < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : D.R.k + ↑j + s + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t := by omega
    simp only [c3, if_true] at hq
    rw [hp, hmj] at hq
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k + j + s : ℕ) : ℚ) =
        -(D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ + ((D.R.t : ℚ) - 1) / 2 - s := by
      push_cast at hq he ⊢
      linarith
    have hwj : wj D ((j : ℕ) + 1) τ = (((D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dif_pos hj.2]
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    rw [hwj]
    push_cast at this ⊢
    linarith
  · intro i hi
    have hal : D.R.k - 1 + i + D.R.t < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : ¬ (D.R.k - 1 + (i : ℕ) + D.R.t + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t) := by omega
    simp only [c3, if_false] at hq
    rw [show D.R.m - ((j : ℕ) + 1) + 1 - (D.R.m - ((j : ℕ) + 1) + 1 - (D.R.k - 1 + (i : ℕ) + D.R.t + 1 - (D.R.k + ((j : ℕ) + 1) - 1) - D.R.t))
        = (i : ℕ) - j by omega] at hq
    rw [show (j : ℕ) + 1 + ((i : ℕ) - j) = (i : ℕ) + 1 by omega, hp, hmj] at hq
    have hij : (((i : ℕ) - (j : ℕ) : ℕ) : ℚ) = (i : ℚ) - j := by
      rw [Nat.cast_sub (by omega)]
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i + D.R.t : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, Nat.cast_add, hk1]
      rw [hij] at hq
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this

end GlobalTheory.ExpTie.Lift

end
