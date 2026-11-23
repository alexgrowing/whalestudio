import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker

namespace GlobalTheory.Phase.Doubling

noncomputable section

variable {n g : ℕ}

def rowM (j : Fin 2) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : Matrix (Fin n) (Fin g) ℚ :=
  Matrix.of fun k i => x j (k, i)

def glue (a b : Matrix (Fin n) (Fin g) ℚ) : Matrix (Fin 2) (Fin n × Fin g) ℚ :=
  Matrix.of fun j p => if j = 0 then a p.1 p.2 else b p.1 p.2

theorem rowM_glue_zero (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 0 (glue a b) = a := by
  ext k i; simp [rowM, glue]

theorem rowM_glue_one (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 1 (glue a b) = b := by
  ext k i; simp [rowM, glue]

theorem glue_rowM (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : glue (rowM 0 x) (rowM 1 x) = x := by
  ext j p; fin_cases j <;> simp [rowM, glue]

theorem dup_apply (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    dup φ x = φ (rowM 0 x) * φ (rowM 1 x) := rfl

theorem rowM_add (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x + y) = rowM j x + rowM j y := rfl

theorem rowM_sub (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x - y) = rowM j x - rowM j y := rfl

theorem rowM_smul (j : Fin 2) (c : ℚ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (c • x) = c • rowM j x := rfl

def rowEquiv (n g : ℕ) : Matrix (Fin 2) (Fin n × Fin g) ℚ ≃
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun x := (rowM 0 x, rowM 1 x)
  invFun p := glue p.1 p.2
  left_inv x := glue_rowM x
  right_inv p := by simp [rowM_glue_zero, rowM_glue_one]

theorem dot_row (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    x j ⬝ᵥ y j = ∑ k, rowM j x k ⬝ᵥ rowM j y k := by
  simp [dotProduct, rowM, Fintype.sum_prod_type]

def comp (j : Fin 2) : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ →+
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun y := (rowM j y.1, rowM j y.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def glueP : (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) ×
    (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) →+
    Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ where
  toFun z := (glue z.1.1 z.2.1, glue z.1.2 z.2.2)
  map_zero' := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> simp [glue]
  map_add' a b := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> fin_cases j <;> simp [glue]

theorem comp_glueP_zero (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 0 (glueP (a, b)) = a := by
  show (rowM 0 (glue a.1 b.1), rowM 0 (glue a.2 b.2)) = a
  simp [rowM_glue_zero]

theorem comp_glueP_one (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 1 (glueP (a, b)) = b := by
  show (rowM 1 (glue a.1 b.1), rowM 1 (glue a.2 b.2)) = b
  simp [rowM_glue_one]

theorem glueP_comp (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    glueP (comp 0 y, comp 1 y) = y := by
  show (glue (rowM 0 y.1) (rowM 1 y.1), glue (rowM 0 y.2) (rowM 1 y.2)) = y
  simp [glue_rowM]

theorem om_eq (y y' : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    om y y' = om (comp 0 y) (comp 0 y') + om (comp 1 y) (comp 1 y') := by
  simp only [om, Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib]
  exact add_sub_add_comm _ _ _ _

theorem om_zero_right (y : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) : om y 0 = 0 := by
  simp [om, dotProduct]

theorem heisS_dup (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ)
    (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    heisS y.1 y.2 (dup φ) x = heisS (comp 0 y).1 (comp 0 y).2 φ (rowM 0 x) *
      heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x) := by
  have h : (∑ k, (2 * (x k ⬝ᵥ y.1 k) - y.1 k ⬝ᵥ y.2 k) : ℚ) =
      (∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) +
      (∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) := by
    simp only [Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib, Finset.mul_sum]
    exact add_sub_add_comm _ _ _ _
  unfold heisS
  rw [h, Rat.cast_add, mul_add, Complex.exp_add, dup_apply, rowM_sub, rowM_sub]
  show _ = (φ (rowM 0 x - rowM 0 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) : ℂ))) *
    (φ (rowM 1 x - rowM 1 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) : ℂ)))
  ring

theorem isSB_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) : IsSB (dup φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx j p => ?_, fun x y hy => ?_⟩
  · rw [dup_apply] at hx
    fin_cases j
    · exact h1 _ (left_ne_zero_of_mul hx) p.1 p.2
    · exact h1 _ (right_ne_zero_of_mul hx) p.1 p.2
  · rw [dup_apply, dup_apply, rowM_add, rowM_add, rowM_smul, rowM_smul,
      h2 _ (rowM 0 y) (fun k i => hy 0 (k, i)), h2 _ (rowM 1 y) (fun k i => hy 1 (k, i))]

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨k, hk, hb⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m k,
    pow_mul b, hb, ← pow_mul]

theorem pv_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : PV φ) : PV (dup φ) := by
  obtain ⟨⟨A, ε, hV⟩, hP⟩ := h
  refine ⟨⟨(A.prod A).map glueP, fun y => ε (comp 0 y) * ε (comp 1 y), ?_⟩,
    fun x => ph_mul (hP _) (hP _)⟩
  have mem : ∀ y, y ∈ (A.prod A).map glueP ↔ comp 0 y ∈ A ∧ comp 1 y ∈ A := by
    intro y
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [comp_glueP_zero, comp_glueP_one]
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(comp 0 y, comp 1 y), ⟨ha, hb⟩, glueP_comp y⟩
  refine ⟨?_, fun y => ?_, fun y hy => ?_, fun y hy y' hy' => ?_, ?_, isSB_dup hV.sb, fun y hy => ?_⟩
  · have := (hV.fg.prod hV.fg)
    rw [AddSubgroup.fg_iff] at this ⊢
    obtain ⟨S, hS, hf⟩ := this
    exact ⟨glueP '' S, by rw [← hS, AddMonoidHom.map_closure], hf.image _⟩
  · constructor
    · intro hy y' hy'
      rw [mem] at hy hy'
      obtain ⟨m, hm⟩ := (hV.dual _).1 hy.1 _ hy'.1
      obtain ⟨k, hk⟩ := (hV.dual _).1 hy.2 _ hy'.2
      exact ⟨m + k, by rw [om_eq, hm, hk, Int.cast_add]⟩
    · intro hy
      rw [mem]
      constructor
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (a, 0)) ⟨(a, 0), ⟨ha, A.zero_mem⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, add_zero] at this
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (0, a)) ⟨(0, a), ⟨A.zero_mem, ha⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, zero_add] at this
  · rw [mem] at hy
    rw [norm_mul, hV.norm _ hy.1, hV.norm _ hy.2, one_mul]
  · rw [mem] at hy hy'
    rw [map_add, map_add, hV.semi _ hy.1 _ hy'.1, hV.semi _ hy.2 _ hy'.2, om_eq y y',
      Rat.cast_add, mul_add, Complex.exp_add]
    ring
  · obtain ⟨m, hm, h⟩ := hV.ord
    refine ⟨m, hm, fun y hy => ?_⟩
    rw [mem] at hy
    rw [map_nsmul, map_nsmul, h _ hy.1, h _ hy.2, one_mul]
  · rw [mem] at hy
    funext x
    have h0 := congrFun (hV.fix _ hy.1) (rowM 0 x)
    have h1 := congrFun (hV.fix _ hy.2) (rowM 1 x)
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    rw [heisS_dup, dup_apply, ← h0, ← h1]
    rw [h0, h1]
    linear_combination (ε (comp 1 y) * heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x)) * h0 +
      φ (rowM 0 x) * h1

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) : blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]

theorem blk_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · ext p q
    have := h.1.apply p.2 q.2
    by_cases hpq : p.1 = q.1
    · simp [blk, hpq, this]
    · simp [blk, hpq, Ne.symm hpq]
  · have : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (τ.map Complex.im) := by
      ext p q
      by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [this]
    exact Matrix.PosDef.one.kronecker h.2

theorem blk_inv (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  have : ((blk n τ).map fun z => (z.im : ℂ)) = blk n (τ.map fun z => (z.im : ℂ)) := by
    ext p q
    by_cases h : p.1 = q.1 <;> simp [blk, h]
  rw [this, blk_eq, blk_eq, Matrix.inv_kronecker, inv_one]

theorem expo_row (τ : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin 2 → Fin n × Fin g → ℂ) (j : Fin 2)
    (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    qv (x j) ⬝ᵥ blk n τ *ᵥ qv (x j) + 2 * (qv (x j) ⬝ᵥ ζ j) =
      ∑ k, (qv (rowM j x k) ⬝ᵥ τ *ᵥ qv (rowM j x k) +
        2 * (qv (rowM j x k) ⬝ᵥ (fun k i => ζ j (k, i)) k)) := by
  simp [dotProduct, mulVec, qv, rowM, blk, Fintype.sum_prod_type, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem thS_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin 2 → Fin n × Fin g → ℂ) :
    thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i)) := by
  have s0 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 0 (k, i))
  have s1 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 1 (k, i))
  unfold thS
  rw [tsum_mul_tsum_of_summable_norm s0 s1, ← (rowEquiv n g).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Fin.sum_univ_two, expo_row, expo_row, mul_add, Complex.exp_add, dup_apply]
  simp only [rowEquiv, Equiv.coe_fn_mk]
  ring

theorem doubling : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  intro n g φ
  refine ⟨pv_dup, fun h h' => h ?_, isSB_dup, fun u => ?_, fun τ hτ =>
    ⟨blk_siegel hτ, fun h ζ => thS_dup h hτ ζ, blk_inv τ⟩⟩
  · funext a
    have := congrFun h' (glue a a)
    rw [dup_apply, rowM_glue_zero, rowM_glue_one] at this
    exact mul_self_eq_zero.1 this
  · funext x
    simp only [dup_apply, Pi.smul_apply, smul_eq_mul]
    ring

end

end GlobalTheory.Phase.Doubling
