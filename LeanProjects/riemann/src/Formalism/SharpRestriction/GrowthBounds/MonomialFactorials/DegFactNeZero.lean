import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodCountMem

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem exists_scal (p : ℕ) [hp : Fact p.Prime] (m Mx : ℕ) (hm : m ≠ 0) (h : padicValNat p m ≤ Mx) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) * (m : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
  have hm' : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm
  have hn : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hm', Padic.valuation_natCast]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  refine ⟨⟨(p : ℚ_[p]) ^ Mx / m, ?_⟩, ?_⟩
  · rw [norm_div, norm_pow, Padic.norm_p, hn, div_le_one (zpow_pos hp0 _), inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hp1 (by omega)
  · show (p : ℚ_[p]) ^ Mx / m * m = _
    field_simp

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def expU (a : ℕ) : ℕ := (G.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊

def expM : ℕ := (levels G).sup fun l => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)

theorem lvC_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : lvC (r := r) G j jp ≠ 0 := by
  unfold lvC
  refine mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
    (Nat.factorial_ne_zero _))) (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ?_
      (Nat.factorial_ne_zero _)) (mul_ne_zero ?_ (Nat.factorial_ne_zero _)))
  · exact (Nat.choose_pos (by omega)).ne'
  · exact (Nat.choose_pos (by omega)).ne'

theorem degFact_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : degFact G j jp ≠ 0 := by
  unfold degFact
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)

def nLv (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) : ℕ :=
  goodCount p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D

theorem nLv_mem (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) :
    ∃ x y : Fin (nLv p (r := r) G D l) → MvPolynomial (M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G l.1 l.2) ∧ (∀ i, y i ∈ Ljj p (r := r) G l.1 l.2) ∧
      ∀ i j, fockK (G.phiAll p (r := r) l.1 l.2 (x i)) (y j) =
        (if i = j then (p : ℚ_[p]) ^ D else 0) * (degFact G l.1 l.2 : ℚ_[p]) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D
  refine ⟨x, y, hx, hy, fun i j => ?_⟩
  have hd : (degFact G l.1 l.2 : ℚ_[p]) ≠ 0 := by exact_mod_cast degFact_ne_zero G _ _
  have h := hxy i j
  unfold bejj at h
  rw [div_eq_iff hd] at h
  exact h

theorem blkZ_gen (hB : G.BlockOK) (hr : 1 ≤ r) (U Mx : ℕ)
    (hLL : ∀ x ∈ G.PSZ p (r := r), ((p : ℚ_[p]) ^ U) • x ∈ G.SSZ p (r := r))
    (hM : ∀ l ∈ levels G, padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ Mx) (D : ℤ) :
    ∃ (n : ℕ) (x y : Fin n → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ i, x i ∈ G.SSZ p (r := r)) ∧ (∀ i, y i ∈ G.SSZ p (r := r)) ∧
      (∀ i j, fockK (x i) (y j) =
        if i = j then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0) ∧
      ∑ l ∈ levels G, Module.finrank ℤ_[p] (Ljj p (r := r) G l.1 l.2) ≤
        n + ∑ l ∈ levels G, badLvl p (r := r) G l.1 l.2 D := by
  classical
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hw := fun l : (Fin G.T.t → ℕ) × ℕ => nLv_mem p (r := r) G D l
  choose u v hu hv huv using hw
  have hsc : ∀ l : ↥(levels G), ∃ c : ℤ_[p],
      (c : ℚ_[p]) * ((lvC (r := r) G l.1.1 l.1.2 * degFact G l.1.1 l.1.2 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
    intro l
    exact exists_scal p _ Mx (mul_ne_zero (lvC_ne_zero G _ _) (degFact_ne_zero G _ _)) (hM l.1 l.2)
  choose sc hsc' using hsc
  have hok : ∀ l : ↥(levels G), G.LevelOK l.1.1 l.1.2 := fun l => (Finset.mem_filter.1 l.2).2
  let I := Σ l : ↥(levels G), Fin (nLv p (r := r) G D l.1)
  let Xf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a => ((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (v a.1.1 a.2)
  let Yf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a =>
    sc a.1 • (((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (u a.1.1 a.2))
  have hX : ∀ a, Xf a ∈ G.SSZ p (r := r) := fun a => hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hv _ _))
  have hY : ∀ a, Yf a ∈ G.SSZ p (r := r) := fun a =>
    Submodule.smul_mem _ _ (hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hu _ _)))
  have hXY : ∀ a b : I, fockK (Xf a) (Yf b) = if a = b then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0 := by
    rintro ⟨l, i⟩ ⟨l', k⟩
    simp only [Xf, Yf]
    rw [zsmul_eq, fockK_smul_left, fockK_smul_right, fockK_smul_right]
    by_cases hll : l = l'
    · subst hll
      rw [Th_fock p G hB hr _ _ (hok l) _ _ (hv _ _) (hu _ _), fockK_symm]
      have h1 := huv l.1 k i
      have h2 := hsc' l
      push_cast at h2
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl] at h1
        rw [h1, if_pos rfl]
        rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_natCast, ← h2, two_mul, zpow_add₀ hp0, zpow_natCast]
        ring
      · rw [if_neg (fun h => hik h.symm)] at h1
        rw [h1, if_neg]
        · ring
        · intro h
          rw [Sigma.mk.inj_iff] at h
          exact hik (eq_of_heq h.2)
    · have hne : (l.1.1, l.1.2) ≠ (l'.1.1, l'.1.2) := by
        intro h
        exact hll (Subtype.ext h)
      rw [Th_orth p G hB hr _ _ _ _ (hok l) (hok l') hne _ _ (hv _ _) (hu _ _), if_neg]
      · ring
      · intro h
        rw [Sigma.mk.inj_iff] at h
        exact hll h.1
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => Xf (e.symm i), fun i => Yf (e.symm i), fun i => hX _, fun i => hY _, ?_, ?_⟩
  · intro i j
    rw [hXY]
    simp only [e.symm.injective.eq_iff]
  · have hc : Fintype.card I = ∑ l ∈ levels G, nLv p (r := r) G D l := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort (levels G) (nLv p (r := r) G D)
    rw [hc, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    unfold badLvl bad nLv
    exact le_add_tsub

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
