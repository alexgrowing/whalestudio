import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

namespace ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering

open Submodule Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem babai : ∀ (m : ℕ) (y : Fin m → V) (v : V), v ∈ span ℝ (Set.range y) →
    ∃ x ∈ span ℤ (Set.range y), ‖v - x‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
  have key : ∀ (m : ℕ) (y : Fin m → V) (c : Fin m → ℝ), ∃ n : Fin m → ℤ,
      ‖∑ i, (c i - (n i : ℝ)) • y i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
    intro m
    induction m with
    | zero => intro y c; exact ⟨fun i => i.elim0, by simp⟩
    | succ m ih =>
      intro y c
      obtain ⟨n, hn⟩ := ih (fun i => y i.castSucc) (fun i => c i.castSucc)
      set u := ∑ i : Fin m, (c i.castSucc - (n i : ℝ)) • y i.castSucc with hu
      set w := y (Fin.last m) with hw
      set f := Int.fract (c (Fin.last m)) with hfd
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have havg : (1 - f) * ‖u + f • w‖ ^ 2 + f * ‖u + (f - 1) • w‖ ^ 2 =
          ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_right,
          real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
        ring
      have hq : f * (1 - f) ≤ 1 / 4 := by nlinarith [sq_nonneg (f - 1 / 2)]
      have hbound : ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        have h1 := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖w‖)
        nlinarith [hn]
      have hsplit : ∀ N : ℤ, ∑ i, (c i - ((Fin.snoc (α := fun _ => ℤ) n N i : ℤ) : ℝ)) • y i =
          u + (c (Fin.last m) - (N : ℝ)) • w := by
        intro N
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hu, hw]
      by_cases hc : ‖u + f • w‖ ^ 2 ≤ ‖u + (f - 1) • w‖ ^ 2
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n ⌊c (Fin.last m)⌋, ?_⟩
        rw [hsplit, ← Int.fract]
        nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hc)]
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n (⌊c (Fin.last m)⌋ + 1), ?_⟩
        have e : c (Fin.last m) - (((⌊c (Fin.last m)⌋ + 1 : ℤ)) : ℝ) = f - 1 := by
          rw [hfd, Int.fract]
          push_cast
          ring
        rw [hsplit, e]
        push_neg at hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hf1.le) (sub_nonneg.mpr hc.le)]
  intro m y v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  obtain ⟨n, hn⟩ := key m y c
  refine ⟨∑ i, (n i) • y i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  have e : v - ∑ i, (n i) • y i = ∑ i, (c i - (n i : ℝ)) • y i := by
    rw [← hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hn

theorem cover {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) (v : V) :
    ∃ x ∈ span ℤ (Set.range b),
      ‖v - x‖ ^ 2 ≤ (finrank ℝ V : ℝ) / 4 * ((finrank ℝ V : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  set n := finrank ℝ V with hn
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm
  have hli : LinearIndependent ℝ bd := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (b i)) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  let Bd : Basis ι ℝ V := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  have hBd : ∀ i, Bd i = bd i := fun i => Basis.mk_apply _ _ _
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ V).repr
  let B' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Bd.reindex e).map φ.toLinearEquiv
  have hB' : ∀ j, B' j = φ (bd (e.symm j)) := fun j => by simp [B', hBd]
  have hmin' : ∀ x ∈ span ℤ (Set.range B'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • B' i) = φ (∑ i, c i • bd (e.symm i)) := by
      simp [hB', map_sum, map_zsmul]
    have hwmem : (∑ i, c i • bd (e.symm i)) ∈ span ℤ (Set.range bd) :=
      sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self _)) _
    rw [hw, LinearIsometryEquiv.norm_map]
    refine hmin _ hwmem ?_
    intro h0
    apply hx0
    rw [hw, h0, map_zero]
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual B' lam hlam hmin'
  let yV : Fin n → V := fun i => φ.symm (y i)
  have hyVint : ∀ i k, ∃ m : ℤ, inner ℝ (yV i) (bd k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := hyint i (e k)
    refine ⟨m, ?_⟩
    rw [← hm, hB', Equiv.symm_apply_apply, ← LinearIsometryEquiv.inner_map_map φ]
    simp [yV]
  have hyVmem : ∀ i, yV i ∈ span ℤ (Set.range b) := by
    intro i
    have hrep : ∀ k, b.repr (yV i) k = inner ℝ (yV i) (bd k) := by
      intro k
      have h : inner ℝ (yV i) (bd k) = ∑ l, b.repr (yV i) l * inner ℝ (b l) (bd k) := by
        conv_lhs => rw [← b.sum_repr (yV i)]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
      rw [h]
      simp [hd]
    rw [← b.sum_repr (yV i)]
    refine sum_mem fun k _ => ?_
    obtain ⟨m, hm⟩ := hyVint i k
    rw [hrep, hm, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (subset_span (Set.mem_range_self k)) m
  have hyVli : LinearIndependent ℝ yV :=
    hyli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker
  have hspan : span ℝ (Set.range yV) = ⊤ :=
    hyVli.span_eq_top_of_card_eq_finrank' (by simp [n])
  obtain ⟨x, hx, hxb⟩ := babai n yV v (hspan ▸ mem_top)
  refine ⟨x, span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyVmem i) hx, hxb.trans ?_⟩
  calc (1 / 4) * ∑ i, ‖yV i‖ ^ 2 ≤ (1 / 4) * ∑ _i : Fin n, ((n : ℝ) ^ 2 / lam) ^ 2 := by
        gcongr with i
        have : ‖yV i‖ = ‖y i‖ := by simp [yV]
        rw [this]
        exact hynorm i
    _ = (n : ℝ) / 4 * ((n : ℝ) ^ 2 / lam) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
