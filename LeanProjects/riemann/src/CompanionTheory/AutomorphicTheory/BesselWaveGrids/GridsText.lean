import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq

section shift

variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ} {l n₀ : ℕ}

theorem pairData_plus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uPlus P.u l n₀)) (l + 1) (lamN lam) c g b := by
  refine (movedData_of_hyp (P := shP P P.u (uPlus P.u l n₀)) h hu (by omega) hlk (fun i hi => ?_) ?_).toPair
  · show uPlus P.u l n₀ i = P.u i
    simp only [uPlus, if_neg hi]
  · show |uPlus P.u l n₀ (l + 1)| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uPlus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem pairData_minus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uMinus P.u l n₀)) l (lamN lam) c g b := by
  refine (movedData_of_hyp (P := shP P P.u (uMinus P.u l n₀)) h hu hl1 hlk.le (fun i hi => ?_) ?_).toPair
  · show uMinus P.u l n₀ i = P.u i
    simp only [uMinus, if_neg hi]
  · show |uMinus P.u l n₀ l| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uMinus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem len_le (r : ℕ) : 15 * ((r : ℝ) + 1) * (2 * r + 1) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith

end shift

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grids_PStar (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 (lamN lam) c g b)
    (hlen : 15 * ((P.r : ℝ) + 1) * (2 * P.r + 1) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  have e : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r (lamN lam) c = PStar lam c :=
    funext fun y => Pst_lamN P.k P.r lam c y
  rw [← e]
  refine grids_text p 3 (3 * (P.r + 1)) (by omega) (lamN lam) c g b hL (le_trans (le_of_eq ?_) hlen)
  push_cast
  ring

theorem gridΛ_bounds (p : KB.Pl P Wp Wq) (b CT : ℝ) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    1 ≤ gridΛ P b (3 * (P.r + 1)) ∧ gridΛ P b (3 * (P.r + 1)) ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
  ⟨one_le_gridΛ _ _ _, gridΛ_le P b CT _ le_rfl hb hCT (mul_pos p.hP.1.T_pos p.hP.1.T'_pos) hTT⟩

theorem grids_diff (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b)
    (hlen : 30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) :=
  grids_PStar p lam c g b ((lamData_of_hyp h hu hu').toPair p.hl.1 p.hl.2.1) ((len_le P.r).trans hlen)

theorem grids_plus {up up' : ℕ → ℝ} (q : KB.Pl (shP P up up') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : up = P.u) (e2 : up' = uPlus P.u l n₀)
    (e3 : q.l0 = l + 1) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_plus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u (l + 1) - uPlus P.u l n₀ (l + 1)|
  simp only [uPlus, if_true]
  rw [show P.u (l + 1) - (P.u (l + 1) + n₀) = -(n₀ : ℝ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

theorem grids_minus {um um' : ℕ → ℝ} (q : KB.Pl (shP P um um') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : um = P.u) (e2 : um' = uMinus P.u l n₀)
    (e3 : q.l0 = l) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_minus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u l - uMinus P.u l n₀ l|
  simp only [uMinus, if_true]
  rw [show P.u l - (P.u l - n₀) = (n₀ : ℝ) by ring, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

end grid

end CompanionTheory.WaveGrid
