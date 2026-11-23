import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixIntegralIntegrableLinear

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

noncomputable section
namespace GlobalTheory.GamMul.Cong

section Ring
variable {R : Type} [CommRing R] {m m₁ m₂ : ℕ}

theorem put_mul_put (y z : Matrix (Fin m₁) (Fin m₂) R) : put m 0 m₁ y * put m 0 m₁ z = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [put, Matrix.of_apply]
  split_ifs with h1 h2
  · omega
  all_goals simp

theorem uni_val (y : Matrix (Fin m₁) (Fin m₂) R) :
    (uni m 0 m₁ y).val = 1 + put m 0 m₁ y ∧ ((uni m 0 m₁ y)⁻¹).val = 1 - put m 0 m₁ y := by
  let u : GL (Fin m) R := ⟨1 + put m 0 m₁ y, 1 - put m 0 m₁ y,
    by simp [add_mul, mul_sub, put_mul_put], by simp [sub_mul, mul_add, put_mul_put]⟩
  have : uni m 0 m₁ y = u := toGL_val u
  rw [this]
  exact ⟨rfl, rfl⟩

theorem put_inl_inr (h : m₁ + m₂ = m) (y : Matrix (Fin m₁) (Fin m₂) R) (i : Fin m₁) (j : Fin m₂) :
    put m 0 m₁ y (stdSum h (.inl i)) (stdSum h (.inr j)) = y i j := by
  simp only [put, Matrix.of_apply]
  rw [dif_pos (by simp)]
  congr 1 <;> ext <;> simp

theorem put_inr (h : m₁ + m₂ = m) (y : Matrix (Fin m₁) (Fin m₂) R) (i : Fin m₂) (j : Fin m) :
    put m 0 m₁ y (stdSum h (.inr i)) j = 0 := by
  simp only [put, Matrix.of_apply]
  rw [dif_neg (by simp)]

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_bd {a b d : Type} [Fintype b] {X : Matrix a b k} {Y : Matrix b d k} {s t : ValueGroupWithZero k}
    (hX : ∀ i j, valuation k (X i j) ≤ s) (hY : ∀ i j, valuation k (Y i j) ≤ t) (i : a) (j : d) :
    valuation k ((X * Y) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hX i l) (hY l j)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem solve_bd {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a k} (hA : ∀ i j, valuation k ((A - 1) i j) < 1)
    {x : a → k} {s : ValueGroupWithZero k} (hb : ∀ i, valuation k ((A *ᵥ x) i) ≤ s) (i : a) :
    valuation k (x i) ≤ s := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i)) ⟨i, Finset.mem_univ _⟩
  refine (hi₀ i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < valuation k (x i₀) := lt_of_le_of_lt zero_le hlt
  have e : x i₀ = (A *ᵥ x) i₀ - ((A - 1) *ᵥ x) i₀ := by simp [Matrix.sub_mulVec]
  have h1 : valuation k (((A - 1) *ᵥ x) i₀) < valuation k (x i₀) := by
    simp only [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_lt _ h0.ne' fun l _ => ?_
    rw [map_mul]
    calc _ ≤ valuation k ((A - 1) i₀ l) * valuation k (x i₀) := mul_le_mul' le_rfl (hi₀ l (Finset.mem_univ _))
      _ < 1 * valuation k (x i₀) := mul_lt_mul_of_pos_right (hA _ _) h0
      _ = _ := one_mul _
  have h2 := Valuation.map_sub_lt (valuation k) ((hb i₀).trans_lt hlt) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isUnit_of_near {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a k}
    (hA : ∀ i j, valuation k ((A - 1) i j) < 1) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  rw [← sub_eq_zero]
  funext i
  have := solve_bd hA (x := x - y) (s := 0) (fun i => by simp [Matrix.mulVec_sub, hxy]) i
  simpa using this

theorem bd_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) (i j : n) :
    valuation k (g.val i j) ≤ 1 := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1 i j

def congK (m : ℕ) (c : kˣ) : Subgroup (GL (Fin m) k) where
  carrier := {g | g ∈ KO k (Fin m) ∧ g.val - 1 ∈ box m m c}
  one_mem' := ⟨one_mem _, fun i j => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨mul_mem hx hy, fun i j => ?_⟩
    have e : (x * y).val - 1 = (x.val - 1) * y.val + (y.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_le _ (by simpa using mul_bd hx' (bd_KO hy) i j) (hy' i j)
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨inv_mem hx, fun i j => ?_⟩
    have e : (x⁻¹).val - 1 = -((x.val - 1) * (x⁻¹).val) := by
      rw [sub_mul, Units.mul_inv]; noncomm_ring
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    simpa using mul_bd hx' (bd_KO (inv_mem hx)) i j

theorem isOpen_congK (m : ℕ) (c : kˣ) : IsOpen (congK m c : Set (GL (Fin m) k)) := by
  have hb : IsOpen (box m m c) := by rw [box_eq_standard_box]; exact GlobalTheory.LocMod.Inhab.isOpen_box c
  exact GlobalTheory.SplitFlip.isOpen_KO.inter
    (hb.preimage (f := fun g : GL (Fin m) k => g.val - 1) (Units.continuous_val.sub continuous_const))

theorem conj_mem_congK (m : ℕ) (c : kˣ) {x y : GL (Fin m) k} (hx : x ∈ KO k (Fin m)) (hy : y ∈ congK m c) :
    x * y * x⁻¹ ∈ congK m c := by
  refine ⟨mul_mem (mul_mem hx hy.1) (inv_mem hx), fun i j => ?_⟩
  have e : (x * y * x⁻¹).val - 1 = x.val * (y.val - 1) * (x⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
  rw [e]
  simpa using mul_bd (mul_bd (bd_KO hx) hy.2) (bd_KO (inv_mem hx)) i j

theorem uni_mem_congK {m m₁ m₂ : ℕ} {c : kˣ} (hc : valuation k (c : k) ≤ 1) {y : Matrix (Fin m₁) (Fin m₂) k}
    (hy : y ∈ box m₁ m₂ c) : uni m 0 m₁ y ∈ congK m c := by
  have hp : ∀ i j, valuation k (put m 0 m₁ y i j) ≤ valuation k (c : k) := fun i j => by
    simp only [put, Matrix.of_apply]
    split_ifs
    · exact hy _ _
    · simp
  have h1 : ∀ i j, valuation k ((1 : Matrix (Fin m) (Fin m) k) i j) ≤ 1 := bd_KO (one_mem _)
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [(uni_val y).1]
    exact Valuation.map_add_le (valuation k) (h1 i j) ((hp i j).trans hc)
  · rw [(uni_val y).2]
    exact Valuation.map_sub_le (valuation k) (h1 i j) ((hp i j).trans hc)
  · rw [(uni_val y).1, add_sub_cancel_left]
    exact hp i j

theorem factor_congK {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {c : kˣ} (hc : valuation k (c : k) < 1) {g : GL (Fin m) k}
    (hg : g ∈ congK m c) : ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ box m₁ m₂ c, g = p * uni m 0 m₁ y := by
  set e := stdSum h with he
  let A : Matrix (Fin m₁) (Fin m₁) k := Matrix.of fun i j => g.val (e (.inl i)) (e (.inl j))
  let B : Matrix (Fin m₁) (Fin m₂) k := Matrix.of fun i j => g.val (e (.inl i)) (e (.inr j))
  have hA : ∀ i j, valuation k ((A - 1) i j) < 1 := fun i j => by
    have := (hg.2 (e (.inl i)) (e (.inl j))).trans_lt hc
    simpa [A, Matrix.one_apply] using this
  have hB : ∀ i j, valuation k (B i j) ≤ valuation k (c : k) := fun i j => by
    have := hg.2 (e (.inl i)) (e (.inr j))
    simpa [B, Matrix.one_apply] using this
  obtain ⟨a, ha⟩ := isUnit_of_near hA
  have hy : A * ((a⁻¹).val * B) = B := by rw [← ha, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  generalize (a⁻¹).val * B = y at hy
  refine ⟨g * (uni m 0 m₁ y)⁻¹, (mem_parabLower_two k).2 fun i j => ?_, y, fun i j => ?_, by simp⟩
  · rw [Units.val_mul, (uni_val y).2, mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_apply, ← e.sum_comp,
      Fintype.sum_sum_type]
    simp only [he, put_inl_inr, put_inr, mul_zero, Finset.sum_const_zero, add_zero]
    have := congrFun (congrFun hy i) j
    rw [Matrix.mul_apply] at this
    exact sub_eq_zero.2 this.symm
  · refine solve_bd hA (x := fun l => y l j) (fun l => ?_) i
    have := hB l j
    rw [← hy] at this
    exact this

theorem exists_congK_subset (m : ℕ) {U : Set (GL (Fin m) k)} (hU : U ∈ nhds (1 : GL (Fin m) k)) :
    ∃ c : kˣ, valuation k (c : k) < 1 ∧ (congK m c : Set (GL (Fin m) k)) ⊆ U := by
  rw [GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hc : Continuous fun X : Matrix (Fin m) (Fin m) k => X + 1 := continuous_id.add continuous_const
  have hV' : (fun X : Matrix (Fin m) (Fin m) k => X + 1) ⁻¹' V ∈ nhds (0 : Matrix (Fin m) (Fin m) k) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨c, hc⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hV'
  obtain ⟨d, hd0, hd1⟩ : ∃ d : k, d ≠ 0 ∧ valuation k d < 1 := by
    obtain ⟨d, h1, h2⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    exact ⟨d, by simpa using h1, h2⟩
  have key : ∀ c' : kˣ, valuation k (c' : k) ≤ valuation k (c : k) → (congK m c' : Set (GL (Fin m) k)) ⊆ U := by
    intro c' h g hg
    refine hVU ?_
    have := hc _ (box_mono m m h hg.2)
    simpa using this
  rcases le_total (valuation k (c : k)) (valuation k d) with h | h
  · exact ⟨c, h.trans_lt hd1, key c le_rfl⟩
  · exact ⟨Units.mk0 d hd0, hd1, key _ h⟩

theorem exists_cong_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m m₁ m₂ : ℕ) (h : m₁ + m₂ = m), ∀ U ∈ nhds (1 : GL (Fin m) k), ∃ (c : kˣ) (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) ∧ IsCompact (K : Set (GL (Fin m) k)) ∧ (K : Set (GL (Fin m) k)) ⊆ U ∧ K ≤ KO k (Fin m) ∧ (∀ x ∈ KO k (Fin m), ∀ y ∈ K, x * y * x⁻¹ ∈ K) ∧ (∀ y ∈ box m₁ m₂ c, uni m 0 m₁ y ∈ K) ∧ (∀ g ∈ K, ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ box m₁ m₂ c, g = p * uni m 0 m₁ y) ∧ IsOpen (KO k (Fin m) : Set (GL (Fin m) k)) ∧ IsCompact (KO k (Fin m) : Set (GL (Fin m) k)) := by
  intro k _ _ _ _ m m₁ m₂ h U hU
  obtain ⟨c, hc, hK⟩ := exists_congK_subset m hU
  exact ⟨c, congK m c, isOpen_congK m c,
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_congK m c)) fun _ hg => hg.1,
    hK, fun _ hg => hg.1, fun x hx y hy => conj_mem_congK m c hx hy, fun y hy => uni_mem_congK hc.le hy,
    fun g hg => factor_congK h hc hg, GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩

end GlobalTheory.GamMul.Cong
