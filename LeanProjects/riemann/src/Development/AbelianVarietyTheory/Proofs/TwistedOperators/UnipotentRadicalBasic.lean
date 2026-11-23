import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Radical

section
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def Uni (b : ι → ℕ) (M : Matrix ι ι k) : Prop :=
  ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s

omit [Fintype ι] in
theorem Uni.blockTri {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.BlockTriangular b := by
  intro r s hrs
  rw [h r s hrs.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hrs

theorem Uni.mul {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M') :
    Uni b (M * M') := by
  intro r s hrs
  have : (M * M') r s = ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · rw [h r t ht]
    · rw [h'.blockTri (show b s < b t from lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul, h' r s hrs]

theorem Uni.det {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.det = 1 := by
  rw [h.blockTri.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [h r s (by rw [hr, hs])]
    simp [Matrix.one_apply]
  rw [this, Matrix.det_one]

theorem Uni.inv {b : ι → ℕ} {g : GL ι k} (h : Uni b g.val) : Uni b (g⁻¹).val := by
  have hb : (g⁻¹).val.BlockTriangular b := by
    letI : Invertible g.val := g.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri
  intro r s hrs
  have : ((g⁻¹).val * g.val) r s = ((g⁻¹).val * (1 : Matrix ι ι k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b s) (b t) with ht | ht
    · rw [h t s ht]
    · rw [hb (show b t < b r from lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [Matrix.mul_one, Units.inv_mul] at this
  exact this.symm

theorem Uni.mul_apply_succ {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M')
    {r s : ι} (hrs : b s = b r + 1) : (M * M') r s = M r s + M' r s := by
  have e : (M * M') r s = (M * (1 : Matrix ι ι k)) r s + ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · have hts : t ≠ s := by
        rintro rfl
        omega
      rw [h r t ht, Matrix.one_apply_ne hts, mul_zero, zero_add]
    · have hrt : r ≠ t := by
        rintro rfl
        omega
      rw [h' t s (by omega), Matrix.one_apply_ne hrt, zero_mul, add_zero]
  rw [e, Matrix.mul_one, Matrix.one_mul]

end

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem mem_N_iff (g : GL (n ⊕ Fin c) k) : g ∈ N k n c p ↔ InN p g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro r s _; rfl
    | mul x y _ _ hx hy => exact Uni.mul (b := lev p) hx hy
    | inv x _ hx => exact Uni.inv (b := lev p) hx
  · intro hg
    exact Subgroup.subset_closure hg

theorem simpleSum_mul {g h : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (hh : h ∈ N k n c p) :
    simpleSum (g * h) = simpleSum g + simpleSum h := by
  rw [mem_N_iff] at hg hh
  simp only [simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Uni.mul_apply_succ (b := lev p) hg hh (by simp [lev, hij])
  · simp

theorem embX_val (x : GL n k) : (embX c x).val = fromBlocks x.val 0 0 1 := rfl

theorem toBlocks₁₁_of_mem {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    g.val.toBlocks₁₁ = 1 := by
  rw [mem_N_iff] at hg
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [hg _ _ (by simp [lev])]
  simp [Matrix.one_apply]

theorem conj_val (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    (embX c x * g * (embX c x)⁻¹).val =
      fromBlocks (x.val * g.val.toBlocks₁₁ * (x⁻¹).val) (x.val * g.val.toBlocks₁₂)
        (g.val.toBlocks₂₁ * (x⁻¹).val) g.val.toBlocks₂₂ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, embX_val, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]

theorem conj_mem (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    embX c x * g * (embX c x)⁻¹ ∈ N k n c p := by
  have h11 := toBlocks₁₁_of_mem hg
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rw [conj_val, h11, Matrix.mul_one, Units.mul_inv]
  rcases r with r | r <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inl t) (Sum.inr s) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₁₂, this]
  · rw [fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inr r) (Sum.inl t) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₂₁, this]
  · rw [fromBlocks_apply₂₂]
    exact hg _ _ hrs

theorem simpleSum_conj (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g := by
  simp only [simpleSum, conj_val, fromBlocks_apply₂₂]
  rfl

theorem exists_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, g, hg, rfl⟩ ⟨y, h, hh, rfl⟩
        refine ⟨x * y, _, mul_mem (conj_mem y⁻¹ hg) hh, ?_⟩
        rw [map_mul, map_inv]
        group
      inv_mem' := by
        rintro _ ⟨x, g, hg, rfl⟩
        refine ⟨x⁻¹, _, conj_mem x (inv_mem hg), ?_⟩
        rw [map_inv]
        group }
  have : R k n c p ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, 1, one_mem _, (mul_one _).symm⟩
    · intro g hg
      exact ⟨1, g, hg, by simp⟩
  exact this hr

theorem toBlocks₁₁_embX_mul (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    (embX c x * g).val.toBlocks₁₁ = x.val := by
  rw [Units.val_mul, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp [fromBlocks_multiply, toBlocks₁₁_of_mem hg]

theorem existsUnique_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k) := by
  obtain ⟨x, g, hg, rfl⟩ := exists_of_mem_R hr
  refine ⟨(x, ⟨g, hg⟩), rfl, ?_⟩
  rintro ⟨y, h, hh⟩ e
  have hxy : y = x := by
    apply Units.ext
    rw [← toBlocks₁₁_embX_mul x hg, ← toBlocks₁₁_embX_mul y hh]
    exact congrArg (fun u : GL (n ⊕ Fin c) k => u.val.toBlocks₁₁) e.symm
  subst hxy
  have : g = h := mul_left_cancel e
  subst this
  rfl

theorem simpleSum_eq_zero {g : GL (n ⊕ Fin c) k}
    (h : ∀ i j, g.val (Sum.inr i) (Sum.inr j) = (1 : Matrix (Fin c) (Fin c) k) i j) :
    simpleSum g = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rw [h, Matrix.one_apply_ne]
    rintro rfl
    omega
  · rfl

theorem rowE_mem {l : ℕ} (u : n → k) (hl : l < p) : rowE c l u ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [rowE, lowU, Matrix.one_apply]
  · simp [rowE, lowU]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (r.val + 1 = l) := by omega
    simp [rowE, lowU, this]
  · simp [rowE, lowU, Matrix.one_apply]

theorem colE_mem {i : ℕ} (β : n → k) (hi : p < i) : colE c i β ∈ N k n c p := by
  rw [mem_N_iff]
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : ¬ (s.val + 1 = i) := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem unipotent_radical_basic : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ N k n c p ↔ InN p g) ∧ (∀ g ∈ N k n c p, ∀ h ∈ N k n c p, simpleSum (g * h) = simpleSum g + simpleSum h) ∧ (∀ g ∈ N k n c p, Matrix.GeneralLinearGroup.det g = 1) ∧ (∀ (x : GL n k), ∀ g ∈ N k n c p, embX c x * g * (embX c x)⁻¹ ∈ N k n c p ∧ simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g) ∧ (∀ r ∈ R k n c p, ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k)) ∧ (∀ (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k), (∀ r s, lev p s ≤ lev p r → M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) → M.det = 1) ∧ (∀ (l : ℕ) (u : n → k), l < p → rowE c l u ∈ N k n c p ∧ simpleSum (rowE c l u) = 0) ∧ ∀ (i : ℕ) (β : n → k), p < i → colE c i β ∈ N k n c p ∧ simpleSum (colE c i β) = 0 := by
  intro k _ n _ _ c p
  refine ⟨mem_N_iff, fun g hg h hh => simpleSum_mul hg hh, fun g hg => ?_,
    fun x g hg => ⟨conj_mem x hg, simpleSum_conj x g⟩, fun r hr => existsUnique_of_mem_R hr,
    fun M hM => Uni.det (b := lev p) hM,
    fun l u hl => ⟨rowE_mem u hl, simpleSum_eq_zero fun _ _ => rfl⟩,
    fun i β hi => ⟨colE_mem β hi, simpleSum_eq_zero fun _ _ => rfl⟩⟩
  apply Units.ext
  exact Uni.det (b := lev p) ((mem_N_iff g).1 hg)

end GlobalTheory.RootEx.Radical
