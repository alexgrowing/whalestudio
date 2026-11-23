import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.SwSand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts

noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

private theorem SideB_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  simp [unrealify, RL]
  apply Complex.ext <;> simp [realifyFun]

private theorem SideB_le_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

private theorem SideB_lt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

private theorem SideB_below (S : Set (Mat k r)) (x : Mt k r) (t : ℝ) (ht : 0 < t)
    (hlt : rhoS k r S x < ENNReal.ofReal t) :
    ∃ Y : lieE S, (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x ∧
      ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ < t := by
  unfold rhoS at hlt
  obtain ⟨Y, hY⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hex, hY2⟩ := iInf_lt_iff.1 hY
  refine ⟨Y, hex, ?_⟩
  have h3 : ENNReal.ofReal ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ <
      ENNReal.ofReal t := by
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]; exact hY2
  exact (ENNReal.ofReal_lt_ofReal_iff ht).1 h3

theorem SideB_pick (S : Set (Mat k r)) (T : Submodule ℝ (Mat k r)) (hST : lieE S = T.map RL) (x : Mt k r)
    (h : rhoS k r S x ≠ ⊤) (τ : ℝ) (hτ : 0 < τ) :
    ∃ X ∈ T, NormedSpace.exp X = Matrix.of x ∧ ‖RL X‖ ^ 2 < (rhoS k r S x).toReal ^ 2 + τ := by
  have ha : 0 ≤ (rhoS k r S x).toReal := ENNReal.toReal_nonneg
  have hs : 0 < Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ) := Real.sqrt_pos.2 (by positivity)
  have hlt : rhoS k r S x < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
    have e : rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := (ENNReal.ofReal_toReal h).symm
    calc rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := e
      _ < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
        refine (ENNReal.ofReal_lt_ofReal_iff hs).2 ?_
        rw [Real.lt_sqrt ha]; linarith
  obtain ⟨Y, hex, hY⟩ := SideB_below S x _ hs hlt
  have hm : (Y : EuclideanSpace ℝ _) ∈ T.map RL := hST ▸ Y.2
  obtain ⟨X, hX, hXe⟩ := Submodule.mem_map.1 hm
  refine ⟨X, hX, ?_, ?_⟩
  · ext i j; rw [← hex, ← hXe, SideB_unrealify_RL]; rfl
  · rw [hXe]
    exact (Real.lt_sqrt (norm_nonneg _)).1 hY

private theorem SideB_Qreal (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) (q : ℝ) (hq : 0 < q)
    (hQ : Qf k r n c m n' < ENNReal.ofReal q) :
    rhoS k r (Nset k r) n ≠ ⊤ ∧ rhoS k r (UWb k r) m ≠ ⊤ ∧ rhoS k r (Nset k r) n' ≠ ⊤ ∧
      (rhoS k r (Nset k r) n).toReal ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2 + (rhoS k r (UWb k r) m).toReal ^ 2 +
        (rhoS k r (Nset k r) n').toReal ^ 2 < q := by
  have hQt : Qf k r n c m n' ≠ ⊤ := ne_top_of_lt hQ
  unfold Qf at hQt
  have hA : rhoS k r (Nset k r) n ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  have hB : rhoS k r (UWb k r) m ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  have hD : rhoS k r (Nset k r) n' ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  refine ⟨hA, hB, hD, ?_⟩
  have ha : 0 ≤ (rhoS k r (Nset k r) n).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (rhoS k r (UWb k r) m).toReal := ENNReal.toReal_nonneg
  have hd : 0 ≤ (rhoS k r (Nset k r) n').toReal := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ 2 * ∑ a, ‖c a - 1‖ ^ 2 := by positivity
  have e : Qf k r n c m n' = ENNReal.ofReal ((rhoS k r (Nset k r) n).toReal ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2 +
      (rhoS k r (UWb k r) m).toReal ^ 2 + (rhoS k r (Nset k r) n').toReal ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow ha, ENNReal.ofReal_pow hb,
      ENNReal.ofReal_pow hd, ENNReal.ofReal_toReal hA, ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal hD]
    rfl
  rw [e] at hQ
  exact (ENNReal.ofReal_lt_ofReal_iff hq).1 hQ

private theorem SideB_vnorm (X Z X' : Mat k r) (x : Fin r → ℂ) (N : ℝ) (hN0 : 0 ≤ N) (hNR : NormRL)
    (hN2 : N ^ 2 = ‖RL X‖ ^ 2 + 2 * ∑ a, ‖x a‖ ^ 2 + ‖RL Z‖ ^ 2 + ‖RL X'‖ ^ 2) :
    ‖((X, x, Z, X') : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r)‖ ≤ N := by
  have hS : 0 ≤ ∑ a, ‖x a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg ‖x a‖)
  have h1 := sq_nonneg ‖RL X‖
  have h2 := sq_nonneg ‖RL Z‖
  have h3 := sq_nonneg ‖RL X'‖
  have hX : ‖X‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hZ : ‖Z‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hX' : ‖X'‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hx : ‖x‖ ≤ N := by
    refine (pi_norm_le_iff_of_nonneg hN0).2 fun a => SideB_le_of_sq hN0 ?_
    have hxa : ‖x a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖x a‖ ^ 2) (fun a _ => sq_nonneg ‖x a‖)
        (Finset.mem_univ a)
    nlinarith
  first
  | exact norm_prod_le_iff.2 ⟨hX, norm_prod_le_iff.2 ⟨hx, norm_prod_le_iff.2 ⟨hZ, hX'⟩⟩⟩
  | (simp only [Prod.norm_def]; exact max_le hX (max_le hx (max_le hZ hX')))

private theorem SideB_arith (ε ρ N Y : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hρ : 0 < ρ) (hN0 : 0 ≤ N) (hY0 : 0 ≤ Y)
    (hN : N ^ 2 < ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8)) (hY : Y ≤ (1 + ε) * N) : N < ρ ∧ Y < ρ := by
  have e2 : 0 < ε * ε := mul_pos hε0 hε0
  have e3 : 0 < ε * ε * (1 - ε) := mul_pos e2 (sub_pos.2 hε1)
  have e4 : 0 < ε * ε * ε * (1 - ε) := mul_pos (mul_pos e2 hε0) (sub_pos.2 hε1)
  have hf : (1 - ε) ^ 2 + ε ^ 2 / 8 < 1 := by nlinarith
  have hg : (1 + ε) ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) < 1 := by nlinarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hN2 : N ^ 2 < ρ ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hf hρ2]
  have hY2 : Y ^ 2 < ρ ^ 2 := by
    have hq : 0 < (1 + ε) ^ 2 := by positivity
    nlinarith [mul_le_mul hY hY hY0 (by positivity : (0:ℝ) ≤ (1 + ε) * N),
      mul_lt_mul_of_pos_left hN hq, mul_lt_mul_of_pos_left hg hρ2]
  exact ⟨SideB_lt_of_sq hρ.le hN2, SideB_lt_of_sq hρ.le hY2⟩

theorem sideB : SideB := by
  intro hNR hLG hLW hPF hLN hLI hCF k r ε hε0 hε1
  obtain ⟨δ, hδ, hF⟩ := hCF k r ε hε0
  refine ⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hQ => ?_⟩
  have hq : 0 < ((1 - ε) * ρ) ^ 2 := by
    have : 0 < 1 - ε := by linarith
    positivity
  obtain ⟨hA, hB, hD, hQr⟩ := SideB_Qreal n c m n' _ hq hQ
  have hτ : 0 < ρ ^ 2 * ε ^ 2 / 24 := by positivity
  obtain ⟨X, hX, e1, hX2⟩ := SideB_pick (Nset k r) (lieNS k r) (hLN k r) n hA _ hτ
  obtain ⟨Z, hZ, e2, hZ2⟩ := SideB_pick (UWb k r) (uWb k r) (hLW k r).2 m hB _ hτ
  obtain ⟨X', hX', e3, hX'2⟩ := SideB_pick (Nset k r) (lieNS k r) (hLN k r) n' hD _ hτ
  have hv : ((X, c - 1, Z, X') : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) ∈ Vs k r :=
    Submodule.mem_prod.2 ⟨hX, Submodule.mem_prod.2 ⟨Submodule.mem_top, Submodule.mem_prod.2 ⟨hZ, hX'⟩⟩⟩
  have hsum : ∑ i, ‖(c - 1) i‖ ^ 2 = ∑ i, ‖c i - 1‖ ^ 2 := by simp [Pi.sub_apply]
  have hN2 : ‖Lm k r (X, c - 1, Z, X')‖ ^ 2 =
      ‖RL X‖ ^ 2 + 2 * ∑ i, ‖(c - 1) i‖ ^ 2 + ‖RL Z‖ ^ 2 + ‖RL X'‖ ^ 2 := by
    rw [← hNR k r (Lm k r _), (hLI k r).2.2 _ hv]
  have hNlt : ‖Lm k r (X, c - 1, Z, X')‖ ^ 2 < ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) := by
    have e : ((1 - ε) * ρ) ^ 2 + 3 * (ρ ^ 2 * ε ^ 2 / 24) = ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) := by ring
    rw [hN2, hsum]; linarith
  have hvN := SideB_vnorm X Z X' (c - 1) _ (norm_nonneg _) hNR hN2
  obtain ⟨Y, hYu, hYe, hYn⟩ := hF _ hv (by
    have := (SideB_arith ε ρ _ 0 hε0 hε1 hρ (norm_nonneg _) le_rfl hNlt (by positivity)).1
    linarith)
  have hYρ := (SideB_arith ε ρ _ ‖Y‖ hε0 hε1 hρ (norm_nonneg _) (norm_nonneg _) hNlt hYn).2
  have hmem : RL Y ∈ lieE (UH (Hpk k r)) := by
    rw [hLG k r]; exact Submodule.mem_map_of_mem hYu
  unfold gBall expBall
  refine ⟨⟨RL Y, hmem⟩, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    show ‖RL Y‖ < ρ
    rw [hNR k r Y]; exact hYρ
  · have hc : (1 : Fin r → ℂ) + (c - 1) = c := by abel
    funext i j
    show NormedSpace.exp (unrealify (RL Y)) i j = Psi k r n c m n' i j
    rw [SideB_unrealify_RL, hYe, hPF]
    simp only [hc]
    unfold Psi
    rw [e1, e2, e3]

end PI.SwSandwichOfWork
