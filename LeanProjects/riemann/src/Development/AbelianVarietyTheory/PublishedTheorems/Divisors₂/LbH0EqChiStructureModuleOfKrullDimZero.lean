import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section General
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem lbH0_eq_chi_structureModule_of_krullDim_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    {L : LB X} (hL : L.IsLB) : (lbH0 k L : ℤ) = chi k (structureModule X) := by
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have h0 : suppDim (structureModule X) ≤ 0 := by
    unfold suppDim
    exact (topologicalKrullDim_subspace_le _ _).trans (by rw [hD]; simp)
  have : IsFiniteQC (twist (structureModule X) L) := Twist.isFiniteQC_twist hL
  have h1 : suppDim (twist (structureModule X) L) ≤ 0 := by
    rw [Twist.suppDim_twist hL]; exact h0
  rw [lineBundleGlobalSectionsDim_def, ← chi_eq_hdim_zero_of_suppDim_le_zero k h1, chi_twist_of_suppDim_le_zero k h0 hL]

theorem product_nonneg_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    (N : Fin 0 → LB X) : 0 ≤ interNum k (structureModule X) N := by
  rw [interNum_of_isEmpty, ← lbH0_eq_chi_structureModule_of_krullDim_zero hp hD (LB.isLB_triv X)]
  exact Int.natCast_nonneg _

theorem riemannRoch_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    {L : LB X} (hL : L.IsLB) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L 0 : ℝ) * (m : ℝ) ^ 0 / (0 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((0 : ℕ) : ℤ) - 1) := by
  have h : (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L 0 : ℝ) * (m : ℝ) ^ 0 /
      (0 : ℕ).factorial) = fun _ => 0 := by
    funext m
    have e := lbH0_eq_chi_structureModule_of_krullDim_zero hp hD (isLB_lbPow hL m)
    rw [topSelf_zero, ← e]
    simp
  rw [h]
  exact isBigO_zero _ _

theorem product_nonneg_curve [IsIntegral X] (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = (1 : ℕ)) (N : Fin 1 → LB X) (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  have hpr : IsProper (strHom k X) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have e : N = ![N 0] := by
    funext i; fin_cases i; rfl
  rw [e, ← interNumOn_id]
  exact (isNef_iff_isClosedImmersion.1 (hN 0)).2 X (𝟙 X) inferInstance inferInstance
    (by rw [hD]; rfl) (by rw [Category.id_comp]; exact hpr)

end General

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

theorem big_iff_space (N : ℕ) :
    (IsBig k (O1 k N) ↔ 0 < topSelfIntersection k (O1 k N) N) ∧
    (IsBig k (LB.triv (PSpace k (N + 1))) ↔ 0 < topSelfIntersection k (LB.triv (PSpace k (N + 1))) (N + 1)) := by
  refine ⟨iff_of_true (isBig_twistingSheaf k N) (by rw [selfIntersection_O1 k N]; exact one_pos),
    iff_of_false (triv_nef_not_big k N).2.2 ?_⟩
  rw [topSelf_def, interNum_eq_zero_of_cls_eq_zero k _
    (L := fun _ : Fin (N + 1) => LB.triv (PSpace k (N + 1))) (fun _ => LB.isLB_triv _) 0 (cls_triv _)]
  exact lt_irrefl 0

theorem riemannRoch_line :
    (fun m : ℕ => (lbH0 k (lbPow (O1 k 1) m) : ℝ) -
      (topSelfIntersection k (O1 k 1) 1 : ℝ) * (m : ℝ) ^ 1 / (1 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((1 : ℕ) : ℤ) - 1) := by
  have h : (fun m : ℕ => (lbH0 k (lbPow (O1 k 1) m) : ℝ) -
      (topSelfIntersection k (O1 k 1) 1 : ℝ) * (m : ℝ) ^ 1 / (1 : ℕ).factorial) = fun _ => 1 := by
    funext m
    rw [sectionDim_twistingSheaf_pow, selfIntersection_O1 k 1]
    simp
  have h' : (fun m : ℕ => (m : ℝ) ^ (((1 : ℕ) : ℤ) - 1)) = fun _ => 1 := by
    funext m; simp
  rw [h, h']

theorem riemannRoch_plane :
    (fun m : ℕ => (lbH0 k (lbPow (O1 k 2) m) : ℝ) -
      (topSelfIntersection k (O1 k 2) 2 : ℝ) * (m : ℝ) ^ 2 / (2 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((2 : ℕ) : ℤ) - 1) := by
  have h : ∀ m : ℕ, (lbH0 k (lbPow (O1 k 2) m) : ℝ) -
      (topSelfIntersection k (O1 k 2) 2 : ℝ) * (m : ℝ) ^ 2 / (2 : ℕ).factorial = (3 * m + 2) / 2 := by
    intro m
    rw [sectionDim_twistingSheaf_pow, selfIntersection_O1 k 2, Nat.cast_choose_two]
    push_cast
    simp [Nat.factorial]
    ring
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (((2 : ℕ) : ℤ) - 1) = 1 := by norm_num
  rw [h m, he, zpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  linarith

theorem product_neg_line : interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] < 0 := by
  have h1 := O1_isLB k 1
  have hz : (lbZPow (O1 k 1) (-1)).IsLB := Twist.isLB_lbZPow h1 (-1)
  have e : interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] =
      interNum k (structureModule (PSpace k 1))
        (fun i : Fin 1 => lbZPow (O1 k 1) ((fun _ : Fin 1 => (-1 : ℤ)) i)) := by
    refine interNum_congr_cls k _ (fun i => ?_) (fun _ => hz) (fun i => ?_)
    · fin_cases i; exact CechPic.isLB_dual h1
    · fin_cases i
      show cls (dual (O1 k 1)) _ = cls (lbZPow (O1 k 1) (-1)) _
      rw [cls_lbZPow h1, eq_neg_of_add_eq_zero_left (CechPic.cls_dual_add h1)]
      simp
  have hp : ∀ n : ℤ, (chi k (twistZ (structureModule (PSpace k 1)) (O1 k 1) n) : ℚ) =
      (Polynomial.X + 1 : Polynomial ℚ).eval (n : ℚ) := by
    intro n
    have hc : chi k (twistZ (structureModule (PSpace k 1)) (O1 k 1) n) =
        Ring.choose (n + (1 : ℕ)) 1 := ProjCoh.chi_sheafO k 1 n
    rw [hc, Ring.choose_one_right]
    simp
  have key := interNum_lbZPow_of_polynomial k (structureModule (PSpace k 1)) h1
    (Polynomial.X + 1) (by compute_degree!) hp (fun _ : Fin 1 => (-1 : ℤ))
  have hq : (interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] : ℚ) = -1 := by
    rw [e, key]
    simp [Polynomial.coeff_one]
  have : (interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] : ℚ) < 0 := by
    rw [hq]; norm_num
  exact_mod_cast this

end Space

end GlobalTheory.NefNumericsModel
