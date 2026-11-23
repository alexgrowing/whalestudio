import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsClosedS

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

lemma le_one_of_pow_le {x M : ℝ} (h : ∀ m : ℕ, x ^ m ≤ M) : x ≤ 1 := by
  by_contra hx
  push_neg at hx
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt M hx
  linarith [h m]

variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}

lemma modOne (hG : IsMatGroup G) (hD : ModProps G D) : D 1 = 1 := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G := hG.2.1
  have hpos := hD.1 1 h1
  have hm := hD.2.1 1 h1 1 h1
  rw [mul_one] at hm
  exact mul_left_cancel₀ hpos.ne' (hm.symm.trans (mul_one (D 1)).symm)

lemma pow_mem (hG : IsMatGroup G) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G) (n : ℕ) : x ^ n ∈ G := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact hG.2.1
  | succ n ih =>
    rw [pow_succ]
    exact hG.2.2.1 _ ih _ hx

lemma modPow (hG : IsMatGroup G) (hD : ModProps G D) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G)
    (n : ℕ) : D (x ^ n) = D x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact modOne hG hD
  | succ n ih =>
    rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem hG hx n) _ hx, ih]

lemma modEqOne (hG : IsMatGroup G) (hD : ModProps G D) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G)
    (h1 : D x ≤ 1) (h2 : D x⁻¹ ≤ 1) : D x = 1 := by
  have hinv := (hG.2.2.2 x hx).1
  have hxx := (hG.2.2.2 x hx).2
  have hm := hD.2.1 x hx x⁻¹ hinv
  rw [hxx, modOne hG hD] at hm
  have h0 := hD.1 x hx
  have hle : D x * D x⁻¹ ≤ D x := by
    calc D x * D x⁻¹ ≤ D x * 1 := mul_le_mul_of_nonneg_left h2 h0.le
      _ = D x := mul_one _
  linarith

def box1 (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {x | ∀ i j, ‖(x - 1) i j‖ ≤ 1}

lemma isCompact_inter_unit_box (hG : IsClosed G) : IsCompact (G ∩ box1 m) := by
  have hbox : box1 m = Set.pi Set.univ (fun i => Set.pi Set.univ
      (fun j => Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1)) := by
    ext x
    simp only [box1, Set.mem_setOf_eq, Matrix.sub_apply]
    constructor
    · intro h
      show ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1
      intro i _ j _
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h i j
    · intro h i j
      have h' : ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1 := h
      have h2 := h' i (Set.mem_univ _) j (Set.mem_univ _)
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      exact h2
  have hc : IsCompact (box1 m) := by
    rw [hbox]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  exact hc.inter_left hG

theorem trivS_of (hSG : SsetGroup) (hUW : UWCompact) (hN : NGroup) (hNC : NContract) : TrivS := by
  unfold TrivS
  intro k r z hz hT D hD
  have hG := hSG k r z hz hT
  obtain ⟨hN1, hNmul, hNinv⟩ := hN k r
  have h1S : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z := hG.2.1
  obtain ⟨h0, hh0, m0, hm0, he0⟩ := h1S
  have hNS : ∀ n ∈ Nset k r, n ∈ Sset k r z := by
    intro n hn
    refine ⟨h0, hh0, m0 * n, hNmul _ hm0 _ hn, ?_⟩
    rw [← mul_assoc, ← he0, one_mul]
  have hUS : ∀ h ∈ UWset k r z, h ∈ Sset k r z := by
    intro h hh
    exact ⟨h, hh, 1, hN1, (mul_one h).symm⟩
  have hpowN : ∀ n ∈ Nset k r, ∀ j : ℕ, n ^ j ∈ Nset k r := by
    intro n hn j
    induction j with
    | zero =>
      rw [pow_zero]
      exact hN1
    | succ j ih =>
      rw [pow_succ]
      exact hNmul _ ih _ hn
  obtain ⟨M, hM⟩ := hD.2.2.2 _ Set.inter_subset_left (isCompact_inter_unit_box hG.1)
  have hNle : ∀ n ∈ Nset k r, D n ≤ 1 := by
    intro n hn
    apply le_one_of_pow_le (M := M)
    intro j
    have hnj := hpowN n hn j
    obtain ⟨c, hcu, hcS, hcb⟩ := hNC k r z hz (n ^ j) hnj 1 one_pos
    have hnjS := hNS _ hnj
    rw [← modPow hG hD (hNS n hn) j, ← hD.2.2.1 c hcu hcS _ hnjS]
    apply hM
    exact ⟨(hcS _).mpr hnjS, fun i' j' => hcb i' j'⟩
  obtain ⟨M', hM'⟩ := hD.2.2.2 _ (fun h hh => hUS h hh) (hUW k r z hz hT)
  have hSle : ∀ g ∈ Sset k r z, D g ≤ M' := by
    intro g hg
    obtain ⟨h, hh, m, hm, rfl⟩ := hg
    rw [hD.2.1 h (hUS h hh) m (hNS m hm)]
    have h1 := hNle m hm
    have h2 := hD.1 h (hUS h hh)
    have h3 := hM' h hh
    calc D h * D m ≤ D h * 1 := mul_le_mul_of_nonneg_left h1 h2.le
      _ ≤ M' := by
        rw [mul_one]
        exact h3
  have hle1 : ∀ g ∈ Sset k r z, D g ≤ 1 := by
    intro g hg
    apply le_one_of_pow_le (M := M')
    intro j
    rw [← modPow hG hD hg j]
    exact hSle _ (pow_mem hG hg j)
  intro g hg
  exact modEqOne hG hD hg (hle1 g hg) (hle1 _ (hG.2.2.2 g hg).1)

end PI.QuotSetU.UnitaryGroupMassFormula.SW
