import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset MeasureTheory
open scoped InnerProductSpace

private theorem szh_sf_inner_lemma (N : ℕ) (a : Fin N) :
    ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ((N - ((a : ℕ) + 1)).factorial : ℝ) := by
  rw [Finset.prod_nbij (fun b : Fin N => (b : ℕ)) (t := Finset.Ico ((a : ℕ) + 1) N)
    (g := fun j : ℕ => ((j : ℝ) - ((a : ℕ) : ℝ))) ?_ ?_ ?_ ?_]
  · rw [Finset.prod_Ico_eq_prod_range]
    have e : ∀ k ∈ range (N - ((a : ℕ) + 1)),
        ((((a : ℕ) + 1 + k : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((k + 1 : ℕ) : ℝ) := by
      intro k _
      push_cast
      ring
    rw [Finset.prod_congr rfl e, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_Ico]
    exact ⟨hb, b.2⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro j hj
    simp only [Finset.coe_Ico, Set.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show (a : ℕ) < j
    omega
  · intro b _
    rfl

theorem szh_sf (N : ℕ) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range N, (i.factorial : ℝ) := by
  simp_rw [szh_sf_inner_lemma]
  refine (Fin.prod_univ_eq_prod_range (fun i : ℕ => ((N - (i + 1)).factorial : ℝ)) N).trans ?_
  refine Eq.trans ?_ (Finset.prod_range_reflect (fun i : ℕ => (i.factorial : ℝ)) N)
  apply Finset.prod_congr rfl
  intro i _
  show ((N - (i + 1)).factorial : ℝ) = ((N - 1 - i).factorial : ℝ)
  rw [show N - (i + 1) = N - 1 - i by omega]

theorem szh_fdegHC {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) :
    Formalism.QuantumDeterminants.fdegHC lam = vand lam / ∏ i ∈ range N, (i.factorial : ℝ) := by
  unfold Formalism.QuantumDeterminants.fdegHC vand
  rw [szh_sf]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact abs_of_pos (sub_pos.mpr (h hb))

theorem szh_vand_nonneg {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) : 0 ≤ vand lam := by
  unfold vand
  apply Finset.prod_nonneg
  intro a _
  apply Finset.prod_nonneg
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact sub_nonneg.mpr (h hb).le

section Rec

variable (D : D7)

theorem szh_lam_node (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ a.1 < D.R.k - 1) :
    lamSH D.R (D.hc τ) a = -bOne D τ (a.1 - (D.R.k - 1) + 1) := by
  unfold lamSH lamS bOne
  simp [h]
  split_ifs <;> simp

theorem szh_eps_cloud (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 < D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

theorem szh_eps_first (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 = D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

variable {D} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ}

theorem szh_anti (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) : StrictAnti (lamSH D.R (D.hc τ)) := by
  have hr := dimS_eq D.R
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -, -, hCl⟩ := hH
  have hk0 : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hpos : 0 < Cl * ↑D.R.k * ↑D.R.m ^ 4 + ↑D.R.r * ↑D.R.m ^ 10 :=
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hCl hk0) (pow_pos hm0 4)) (by positivity)
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  unfold lamSH
  have h := hd τ (Fin.cast hr (Fin.castSucc i))
    (by have := i.2; simp only [Fin.coe_cast, Fin.coe_castSucc]; omega)
  have e : ∀ hh, (⟨(Fin.cast hr (Fin.castSucc i) : ℕ) + 1, hh⟩ : Fin D.R.r) = Fin.cast hr i.succ :=
    fun hh => Fin.ext (by simp)
  rw [e] at h
  linarith

theorem szh_hc (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) := by
  refine ⟨szh_anti hH τ, fun a => ?_⟩
  obtain ⟨j, hj⟩ := D.R.k_even
  have hn : (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((D.R.rS + j : ℕ) : ℝ) := by
    rw [hj]
    push_cast
    ring
  rw [hn]
  unfold lamSH lamS
  split_ifs with h1 h2
  · obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨_, h1⟩
    exact ⟨z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨_, h2⟩
    exact ⟨-z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · exact ⟨-((D.R.rS + j : ℕ) : ℤ), by push_cast; ring⟩

theorem szh_gap (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ))
      (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  have hr := dimS_eq D.R
  have hrdef : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hkm := D.R.m_add_three_le_k
  have hanti := szh_anti hH τ
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -⟩ := hH
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤
        lamSH D.R (D.hc τ) a - lamSH D.R (D.hc τ) b := by
    intro a b hab he
    have hab' : (a : ℕ) < b := hab
    have hbo := b.2
    have hb1 : ¬ (b : ℕ) < D.R.k - 1 := by
      intro h1
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_cloud D b h1])
    have hb2 : (b : ℕ) ≠ D.R.k - 1 := by
      intro h2
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_first D b h2])
    have hac : a ≤ (⟨(b : ℕ) - 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) := by
      show (a : ℕ) ≤ (b : ℕ) - 1
      omega
    have hlac := hanti.antitone hac
    have e1 := szh_lam_node D τ ⟨(b : ℕ) - 1, by omega⟩ (by show ¬ (b : ℕ) - 1 < D.R.k - 1; omega)
    have e2 := szh_lam_node D τ b hb1
    have i1 : (b : ℕ) - 1 - (D.R.k - 1) + 1 = (b : ℕ) - (D.R.k - 1) := by omega
    simp only [i1] at e1
    have hg := hgap τ ((b : ℕ) - (D.R.k - 1)) (by omega) (by omega)
    linarith
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h hab).trans (le_abs_self _)
  · subst h
    exact absurd rfl hab
  · rw [abs_sub_comm]
    exact (key b a h (Ne.symm hab)).trans (le_abs_self _)

theorem szh_b_sq (large₂ : SizeData₂ D) : large₂.sc.b ^ (2 : ℝ) = Real.exp (2 * large₂.sc.L) := by
  unfold Formalism.BasicNotions.Scale.b
  rw [← Real.exp_mul]
  congr 1
  ring

theorem szh_k_le (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h1 : 1 ≤ Cl) (τ : D.what₂.Tau) :
    (D.R.k : ℝ) ≤ Real.exp (2 * large₂.sc.L) := by
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkC : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ Cl := by
    calc (D.R.k : ℝ) = (D.R.k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (D.R.k : ℝ) ^ Cl := Real.rpow_le_rpow_of_exponent_le hk1 h1
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hH
  have hj := hb τ 1 le_rfl (by have := D.R.two_le_m; omega)
  refine hkC.trans ((le_max_left _ _).trans (hj.1.trans (hj.2.trans (le_of_eq ?_))))
  first
    | exact szh_b_sq large₂
    | (unfold Formalism.BasicNotions.Scale.b; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)

end Rec

end Formalism.MainNotions.BridgeLemma

end
