import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtSolveMapFixedIff

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptNs (G : LogFGL v d) : ℕ → Fin d → MvPowerSeries (Fin d) C
  | 0 => 0
  | n + 1 => fun a => subst (Sum.elim (fun b => X b) (ptNs G n)) (G.F a)

theorem ptNs_const (G : LogFGL v d) : ∀ n a, constantCoeff (ptNs G n a) = 0
  | 0, a => by simp [ptNs]
  | n + 1, a => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (G.F_const a)

theorem ptNs_hasSubst (G : LogFGL v d) (n : ℕ) :
    HasSubst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    cases i with
    | inl b => simp
    | inr b => exact ptNs_const G n b

theorem ptNs_int (G : LogFGL v d) : ∀ n a, ptNs G n a ∈ ptIntSer v (Fin d)
  | 0, a => by simp only [ptNs, Pi.zero_apply]; exact Subring.zero_mem _
  | n + 1, a => by
    refine ptIntSer_subst (ptNs_hasSubst G n) ?_ (G.F_int a)
    rintro (i | i)
    · exact ptIntSer_X i
    · exact ptNs_int G n i

theorem ptNs_lin (G : LogFGL v d) : ∀ (n : ℕ) (a s : Fin d),
    coeff (Finsupp.single s 1) (ptNs G n a) = if s = a then (n : C) else 0
  | 0, a, s => by simp [ptNs]
  | n + 1, a, s => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    show coeff (Finsupp.single s 1) (subst _ (G.F a)) = _
    rw [pt_coeff_single_subst (ptNs_hasSubst G n) h0 (G.F_const a) s, Fintype.sum_sum_type]
    simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, pt_coeff_single_X, ptNs_lin G n,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, add_zero, zero_add,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> push_cast <;> ring

theorem nsmulF_eq_subst (G : LogFGL v d) {ga : Fin d → PowerSeries C}
    (hga : HasSubst ga) : ∀ n, G.nsmulF n ga = fun a => subst ga (ptNs G n a)
  | 0 => by
    funext a
    simp only [LogFGL.nsmulF, ptNs, Pi.zero_apply]
    rw [← substAlgHom_apply hga, map_zero]
  | n + 1 => by
    funext a
    simp only [LogFGL.nsmulF, LogFGL.add, ptNs]
    rw [subst_comp_subst_apply (ptNs_hasSubst G n) hga, nsmulF_eq_subst G hga n]
    congr 1
    funext i
    rcases i with i | i
    · simp [subst_X hga]
    · rfl

theorem isCurve_iff_good {ga : Fin d → PowerSeries C} : IsCurve v ga ↔ PTGood v ga := by
  constructor
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mp (h a).2⟩
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mpr (h a).2⟩

private theorem valuation_natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) (n : ℕ)
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have hcop : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨u, w, huw⟩ := hcop
  have hC : (u : C) * p + (w : C) * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) huw
  have hu : 0 ≤ v (u : C) := intCast_mem (ptIntSub v) u
  have hw : 0 ≤ v (w : C) := intCast_mem (ptIntSub v) w
  have hn0 : 0 ≤ v (n : C) := natCast_mem (ptIntSub v) n
  refine le_antisymm ?_ hn0
  by_contra hpos
  push_neg at hpos
  have h1 : 0 < v ((u : C) * p) := by
    rw [v.map_mul, hvp]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hu)
  have h2 : 0 < v ((w : C) * n) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_left hw)
  have h3 := v.map_add ((u : C) * p) ((w : C) * n)
  rw [hC, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

private theorem exists_eq_single_of_degree_eq_one {σ : Type} (α : σ →₀ ℕ) (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨s, ?_⟩
  have hsum : ∑ i ∈ α.support, α i = 1 := by rw [← h]; rfl
  have hle : α s ≤ 1 := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  have hs1 : α s = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
  have hrest : ∑ i ∈ α.support.erase s, α i = 0 := by
    rw [← Finset.add_sum_erase _ _ hs, hs1] at hsum
    omega
  ext i
  by_cases hi : i = s
  · subst hi
    simp [hs1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne'
    have hmem : i ∈ α.support.erase s :=
      Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hne'⟩
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    omega

theorem nsmul_coprime_bijective_curves [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1)
    (n : ℕ) (hn : ¬ p ∣ n) (gb : Fin d → PowerSeries C) (hgb : IsCurve v gb) :
    ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb := by
  have hn0' : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have hn0 : (n : C) ≠ 0 := by exact_mod_cast hn0'
  have hvn := valuation_natCast_eq_zero_of_not_dvd hp hvp n hn
  have hvinv : (n : C)⁻¹ ∈ ptIntSub v := by
    show 0 ≤ v (n : C)⁻¹
    have h := v.map_mul (n : C) (n : C)⁻¹
    rw [mul_inv_cancel₀ hn0, v.map_one, hvn, zero_add] at h
    rw [← h]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) C, M = (n : C) • 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin d) (Fin d) C, N = (n : C)⁻¹ • 1 := ⟨_, rfl⟩
  have hNM : N * M = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hn0, one_smul]
  have hMN : M * N = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hn0, one_smul]
  have hMab : ∀ a b, M a b = if a = b then (n : C) else 0 := by
    intro a b
    rw [hM, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i j, N i j ∈ ptIntSub v := by
    intro i j
    rw [hN, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact hvinv
    · rw [mul_zero]; exact (ptIntSub v).zero_mem
  have hMint : ∀ a b, M a b ∈ ptIntSub v := by
    intro a b
    rw [hMab]
    split_ifs
    · exact natCast_mem (ptIntSub v) n
    · exact (ptIntSub v).zero_mem
  obtain ⟨K, hK⟩ : ∃ K : Fin d → MvPowerSeries (Fin d) C,
      K = fun b => ptNs G n b - ∑ a, M a b • X a := ⟨_, rfl⟩
  have hK0 : ∀ b, constantCoeff (K b) = 0 := by
    intro b
    simp [hK, ptNs_const]
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := by
    intro b
    rw [hK]
    exact (ptIntSer v (Fin d)).sub_mem (ptNs_int G n b)
      ((ptIntSer v (Fin d)).sum_mem fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hKdeg : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α hα
    left
    by_contra hlt
    push_neg at hlt
    apply hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with hd | hd
    · rw [(Finsupp.degree_eq_zero_iff α).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        hK0 b]
    · obtain ⟨s, rfl⟩ := exists_eq_single_of_degree_eq_one α hd
      rw [hK]
      simp only [map_sub, map_sum, MvPowerSeries.coeff_smul, ptNs_lin, MvPowerSeries.coeff_X,
        Finsupp.single_left_inj one_ne_zero, hMab, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hf : PTGood v gb := isCurve_iff_good.mp hgb
  have key : ∀ y : Fin d → PowerSeries C, PTGood v y →
      (G.nsmulF n y = gb ↔ ∀ b, ∑ a, M a b • y a + subst y (K b) = gb b) := by
    intro y hy
    have hys : HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => (hy a).1
    rw [nsmulF_eq_subst G hys n]
    constructor
    · intro h b
      rw [← congrFun h b, pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), hK]
    · intro h
      funext b
      rw [pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), ← h b, hK]
  obtain ⟨x, ⟨hx, hxeq⟩, huniq⟩ := pt_solve (A := fun x => x) (K := K) (M := M) (N := N) (f := gb)
    hNM hMN hNint hf (fun x hx s => (hx s).1) (fun x hx s => (hx s).2)
    (fun k x y _ _ hxy s e he => hxy s e he) hKdeg hKi hK0
  refine ⟨x, ⟨isCurve_iff_good.mpr hx, (key x hx).mpr hxeq⟩, fun y hy => ?_⟩
  have hyg := isCurve_iff_good.mp hy.1
  exact huniq y ⟨hyg, (key y hyg).mp hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.Sh
