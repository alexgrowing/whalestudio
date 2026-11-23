import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top.HhModel

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem hhFl_monomial (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (a : ℝ) :
    hhFl Ψ N II (monomial m a) = a * ((-1) ^ m.degree * hFlMono Ψ N II m) := by
  have h : (monomial m a : RP Ψ N) = a • basisMonomials (Ψ × Fin N) ℝ m := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h, map_smul, hhFl, Module.Basis.constr_basis, smul_eq_mul]

theorem hhFl_monomial_of_ne (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (a : ℝ)
    (h : m.degree ≠ GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) : hhFl Ψ N II (monomial m a) = 0 := by
  rw [hhFl_monomial, hFlMono, if_neg]
  · simp
  · exact h

theorem testPoly_line : (testPoly 1 : RP Unit 2) = X ((), 1) ^ 2 := by
  have h1 : (Finset.univ.filter (fun i : Fin 2 => 1 ≤ (i : ℕ))) = {1} := by decide
  have h2 : (Finset.univ.filter (fun ab : Fin 2 × Fin 2 => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < 1 ↔ (ab.2 : ℕ) < 1))) = ∅ := by
    decide
  simp only [testPoly, muSmall, fibClass, dimX, h1, h2]
  simp

theorem permExp_eq_iff (σ : Unit → Equiv.Perm (Fin 2)) :
    Finsupp.single ((), (1 : Fin 2)) 1 = permExp σ ↔ σ () = Equiv.swap 0 1 := by
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h ((), 1)
    simp [permExp] at h1
    revert h1
    generalize σ () = s
    revert s
    decide
  · intro h
    ext ⟨⟨⟩, i⟩
    fin_cases i <;> simp [permExp, h]

theorem testDeg_line : testDeg Unit 2 1 = 1 := by
  have h1 : (Finset.univ.filter (fun i : Fin 2 => 1 ≤ (i : ℕ))) = {1} := by decide
  have h2 : (Finset.univ.filter (fun ab : Fin 2 × Fin 2 => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < 1 ↔ (ab.2 : ℕ) < 1))) = ∅ := by
    decide
  have h3 : (muSmall 1 ^ dimX Unit 2 1 * fibClass 1 : RP Unit 2) = X ((), 1) := by
    simp only [muSmall, fibClass, dimX, h1, h2]
    simp
  rw [testDeg, h3, degFl, Finset.sum_eq_single (fun _ => Equiv.swap 0 1)]
  · rw [coeff_X, if_pos ((permExp_eq_iff _).2 rfl)]
    simp [GlobalTheory.CompanionTheory.Ar.Top.dimFl]
  · intro σ _ hσ
    rw [coeff_X, if_neg, mul_zero]
    intro h
    exact hσ (funext fun _ => (permExp_eq_iff σ).1 h)
  · simp

theorem hhTestBound_line (hh : RP Unit 2 → ℝ) : HhTestBound 1 hh ↔ hh (X ((), 1) ^ 2) ≤ Real.log 3 := by
  rw [HhTestBound, testPoly_line, testDeg_line]
  norm_num [dimX]
  constructor <;> intro h <;> linarith

theorem hhTestBound_half : HhTestBound (Ψ := Unit) (N := 2) 1 (fun _ => 1 / 2) := by
  rw [hhTestBound_line]
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
  linarith

theorem not_hhTestBound_two : ¬ HhTestBound (Ψ := Unit) (N := 2) 1 (fun _ => 2) := by
  rw [hhTestBound_line, not_le]
  have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
  linarith

theorem hhFl_testPoly_line (II : IntersectionSystem) :
    hhFl Unit 2 II (testPoly 1) =
      II (FlBlock Unit 2) (FlIdx Unit 2) (PFl Unit 2) 2 (fun _ => xLine Unit 2 ((), 1)) := by
  rw [testPoly_line, X_pow_eq_monomial, hhFl_monomial, hFlMono, if_pos (by simp; rfl)]
  simp only [Finsupp.degree_single, even_two, Even.neg_pow, one_pow, one_mul]
  show II (FlBlock Unit 2) (FlIdx Unit 2) (PFl Unit 2) 2 _ = _
  congr 1
  funext k
  have hl : (Finsupp.toMultiset (Finsupp.single ((), (1 : Fin 2)) 2)).toList.length = 2 := by simp
  unfold GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines
  rw [dif_pos (by rw [hl]; exact k.2)]
  congr 1
  have hm := List.get_mem (Finsupp.toMultiset (Finsupp.single ((), (1 : Fin 2)) 2)).toList ⟨k, by rw [hl]; exact k.2⟩
  rw [Multiset.mem_toList, Finsupp.mem_toMultiset] at hm
  simpa using Finsupp.support_single_subset hm

theorem hhFl_X_pow (II : IntersectionSystem) (p : Ψ × Fin N) :
    hhFl Ψ N II (X p ^ (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1)) = (-1) ^ (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) *
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) (fun _ => xLine Ψ N p) := by
  rw [X_pow_eq_monomial, hhFl_monomial, hFlMono, if_pos (by simp; rfl)]
  simp only [Finsupp.degree_single, one_mul]
  congr 1
  show II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) _ = _
  congr 1
  funext k
  have hl : (Finsupp.toMultiset (Finsupp.single p (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1))).toList.length =
      GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1 := by simp
  unfold GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines
  rw [dif_pos (by rw [hl]; exact k.2)]
  congr 1
  have hm := List.get_mem (Finsupp.toMultiset (Finsupp.single p (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1))).toList
    ⟨k, by rw [hl]; exact k.2⟩
  rw [Multiset.mem_toList, Finsupp.mem_toMultiset] at hm
  simpa using Finsupp.support_single_subset hm

theorem lower_bound_of_base_setting (hL : LowerBoundComponent.Statement) (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ) (B : ℕ) (c : T.Comp) (h3 : 3 * (N - T.j) + 1 ≤ N)
    (hB : 4 * Fintype.card Ψ + 2 ≤ B) (hB' : 4 * Fintype.card Ψ * N ^ 2 ≤ B)
    (hv : 0 ≤ T.vol c * testDeg Ψ N T.j) (h : T.HasBaseDegreeSetting II Ch Cu rd Lval B c) :
    -((Ch + Cu / 2) * Fintype.card Ψ * (N - T.j : ℕ) * bigLam B rd Lval) *
      (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j)) ≤ T.PPc II B c (testPoly T.j) := by
  obtain ⟨K, _, ι, _, Ω, _, _, E, _, _, D, O, Lt, _, _, _, X, hN, hj, hrd, hLv, h1, h2, h4, h5, h6, h7, h8, h9⟩ := h
  have hj' : D.j' = N - T.j := by rw [ComponentData.j', hN, hj]
  have := hL II Ψ K ι Ω E D O Lt X Ch Cu hII h1 h2 h4 h5 h6 h7 (by rw [hj', hN]; exact h3) B hB
    (by rw [hN]; exact hB') h8
  rw [hj', ComponentSetting.La, hrd, hLv] at this
  rw [h9]
  exact mul_le_mul_of_nonneg_right this (mul_nonneg (by positivity) hv)

end GlobalTheory.CompanionTheory.Ar.Top.HhModel
