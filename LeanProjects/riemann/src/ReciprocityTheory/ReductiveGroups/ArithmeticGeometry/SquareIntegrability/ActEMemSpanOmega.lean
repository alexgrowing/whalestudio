import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section act

variable {dim : (E →+* ℂ) → ℕ}

def actE (β : E) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => i.1 β * v i

theorem act_eq_actE (α : 𝓞 E) (v : Vsp dim) : act α v = actE (α : E) v := rfl

@[simp] theorem actE_apply (β : E) (v : Vsp dim) (i : Idx dim) : actE β v i = i.1 β * v i := rfl

theorem actE_add_right (β : E) (v w : Vsp dim) : actE β (v + w) = actE β v + actE β w := by
  ext i
  simp [mul_add]

theorem actE_smul_right (β : E) (c : ℂ) (v : Vsp dim) : actE β (c • v) = c • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem actE_rsmul_right (β : E) (r : ℝ) (v : Vsp dim) : actE β (r • v) = r • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul]
  ring

theorem actE_zero_right (β : E) : actE β (0 : Vsp dim) = 0 := by
  ext i
  simp

theorem actE_add_left (β γ : E) (v : Vsp dim) : actE (β + γ) v = actE β v + actE γ v := by
  ext i
  simp [add_mul]

theorem actE_zero_left (v : Vsp dim) : actE (0 : E) v = 0 := by
  ext i
  simp

theorem actE_one (v : Vsp dim) : actE (1 : E) v = v := by
  ext i
  simp

theorem actE_mul (β γ : E) (v : Vsp dim) : actE (β * γ) v = actE β (actE γ v) := by
  ext i
  simp [mul_assoc]

theorem actE_qsmul (q : ℚ) (β : E) (v : Vsp dim) : actE (q • β) v = (q : ℝ) • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul, Rat.smul_def, map_mul, map_ratCast,
    Complex.ofReal_ratCast]
  ring

theorem act_one' (v : Vsp dim) : act (1 : 𝓞 E) v = v := by
  rw [act_eq_actE]
  simpa using actE_one v

theorem act_mul' (α β : 𝓞 E) (v : Vsp dim) : act (α * β) v = act α (act β v) := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE]
  push_cast
  exact actE_mul _ _ v

theorem norm_actE_le (β : E) (Ω : ℝ) (hΩ : 0 ≤ Ω) (h : ∀ σ : E →+* ℂ, ‖σ β‖ ≤ Ω) (v : Vsp dim) :
    ‖actE β v‖ ≤ Ω * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hΩ, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [actE_apply, norm_mul, mul_pow]
  gcongr
  exact h i.1

theorem actE_mem_of_span (β : E) (S : Set (Vsp dim)) (T : Submodule ℝ (Vsp dim))
    (h : ∀ v ∈ S, actE β v ∈ T) : ∀ v ∈ Submodule.span ℝ S, actE β v ∈ T := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [actE_zero_right]; exact T.zero_mem
  | add x y _ _ hx hy => rw [actE_add_right]; exact T.add_mem hx hy
  | smul r x _ hx => rw [actE_rsmul_right]; exact T.smul_mem r hx

theorem actE_mem_span_omega {n : ℕ} (ω : Fin n → E) {β : E}
    (hβ : β ∈ Submodule.span ℚ (Set.range ω)) (x : Vsp dim) :
    actE β x ∈ Submodule.span ℝ (Set.range fun j => actE (ω j) x) := by
  induction hβ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [actE_zero_left]; exact zero_mem _
  | add y z _ _ hy hz => rw [actE_add_left]; exact add_mem hy hz
  | smul q y _ hy => rw [actE_qsmul]; exact Submodule.smul_mem _ _ hy

variable [IsCMField E]

theorem Hf_actE (β : E) (v w : Vsp dim) :
    Hf (actE β v) w = Hf v (actE (IsCMField.complexConj E β) w) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  ring

theorem Hf_actE' (β : E) (v w : Vsp dim) :
    Hf v (actE β w) = Hf (actE (IsCMField.complexConj E β) v) w := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj]
  ring

end act

end

end ReciprocityTheory.ChartRestriction.G.I2
