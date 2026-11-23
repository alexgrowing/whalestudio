import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegralStatement

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem latA_single_mem {ι : Type} [DecidableEq ι] (j i : ι) : (Pi.single j (1 : L) : ι → L) i ∈ Formalism.UG.intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem latA_dot_mem {ι : Type} [Fintype ι] {u w : ι → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : u ⬝ᵥ w ∈ Formalism.UG.intL L :=
  sum_mem fun i _ => mul_mem (hu i) (hw i)

theorem latA_sum {n m : ℕ} (c : Matrix (Fin n) (Fin n) L) (hc : c.det ≠ 0) (y : Matrix (Fin n) (Fin m) L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_square_matrix_span_columns_integral L n (Fin n ⊕ Fin m) (Matrix.fromCols c y)
  have key : ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
    intro v
    rw [← hb v]
    constructor
    · rintro ⟨u, w, hu, hw, rfl⟩
      refine ⟨Sum.elim u w, ?_, ?_⟩
      · rintro (i | i)
        · exact hu i
        · exact hw i
      · rw [Matrix.fromCols_mulVec_sumElim]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u ∘ Sum.inl, u ∘ Sum.inr, fun i => hu _, fun i => hu _, ?_⟩
      rw [← Matrix.fromCols_mulVec_sumElim, Sum.elim_comp_inl_inr]
  have hcol : ∀ j : Fin n, ∃ t : Fin n → L, c *ᵥ Pi.single j 1 = b *ᵥ t := by
    intro j
    obtain ⟨t, -, ht⟩ := (key (c *ᵥ Pi.single j 1)).1
      ⟨Pi.single j 1, 0, latA_single_mem j, fun _ => zero_mem _, by simp⟩
    exact ⟨t, ht⟩
  choose t ht using hcol
  have hT : b * (Matrix.of t)ᵀ = c := by
    ext i j
    have := congrFun (ht j) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    rfl
  have hdet : b.det ≠ 0 := by
    intro h
    apply hc
    rw [← hT, Matrix.det_mul, h, zero_mul]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero b hdet, key⟩

theorem latA_basis (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ)
    (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := latA_sum (1 : Matrix (Fin n) (Fin n) L) (by simp) xᵀ
  have hN : ∀ u : Fin n → L, ((∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L)) ↔
      ∀ j, ((b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u) j ∈ Formalism.UG.intL L := by
    intro u
    have dual : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) L) (t : Fin k → L), (M *ᵥ t) ⬝ᵥ u = t ⬝ᵥ (Mᵀ *ᵥ u) := by
      intro k M t
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    constructor
    · rintro ⟨h1, h2⟩ j
      obtain ⟨l, w, hl, hw, e⟩ := (hb ((b : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1)).2
        ⟨_, latA_single_mem j, rfl⟩
      have e2 := dual (b : Matrix (Fin n) (Fin n) L) (Pi.single j 1)
      rw [single_one_dotProduct, e, add_dotProduct, dual xᵀ, Matrix.one_mulVec, Matrix.transpose_transpose] at e2
      rw [← e2]
      exact add_mem (latA_dot_mem hl h1) (latA_dot_mem hw h2)
    · intro h
      refine ⟨fun i => ?_, fun k => ?_⟩
      · obtain ⟨t, ht, e⟩ := (hb (Pi.single i 1)).1
          ⟨Pi.single i 1, 0, latA_single_mem i, fun _ => zero_mem _, by
            rw [Matrix.one_mulVec, Matrix.mulVec_zero, add_zero]⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
      · obtain ⟨t, ht, e⟩ := (hb (xᵀ *ᵥ Pi.single k 1)).1
          ⟨0, Pi.single k 1, fun _ => zero_mem _, latA_single_mem k, by simp⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, dual xᵀ, Matrix.transpose_transpose, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
  have hmul : (b : Matrix (Fin n) (Fin n) L)ᵀ * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hmul' : ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (b : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hdet : (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨a, ha⟩ := latA_sum _ hdet y
  refine ⟨a, fun v => ?_⟩
  rw [← ha v]
  constructor
  · rintro ⟨u, w, h1, h2, hw, rfl⟩
    refine ⟨(b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u, w, (hN u).1 ⟨h1, h2⟩, hw, ?_⟩
    rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
  · rintro ⟨u, w, hu, hw, rfl⟩
    have := (hN (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u)).2 (by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]; exact hu)
    exact ⟨_, w, this.1, this.2, hw, rfl⟩

end GlobalTheory.Hk3.HoweG
