import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

private lemma Hf_im_IR_lemma {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) {x y : Vsp dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hI x hx y hy
    | zero => simp [Hf]
    | add y z _ _ h1 h2 =>
      have e : Hf x (y + z) = Hf x y + Hf x z := by
        simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [e, Complex.add_im, h1, h2, add_zero]
    | smul r y _ h =>
      have e : Hf x (r • y) = (r : ℂ) * Hf x y := by
        unfold Hf
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.conj_ofReal]
        ring
      simp [e, h]
  | zero => simp [Hf]
  | add a b _ _ h1 h2 =>
    have e : Hf (a + b) y = Hf a y + Hf b y := by
      simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e, Complex.add_im, h1, h2, add_zero]
  | smul r a _ h =>
    have e : Hf (r • a) y = (r : ℂ) * Hf a y := by
      unfold Hf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
      ring
    simp [e, h]

lemma norm_projection_sq [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) (u : Vsp dim)
    (h1 : Mc σ 1 u ∈ IR I) (hi : Mc σ Complex.I u ∈ IR I) :
    ‖Mc σ 1 u‖ ^ 2 = 2 * ‖prj σ u‖ ^ 2 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  set S1 : ℝ := ∑ i : Idx dim, if i.1 = σ then ‖u i‖ ^ 2 else 0 with hS1
  set S2 : ℝ := ∑ i : Idx dim, if i.1 = ComplexEmbedding.conjugate σ then ‖u i‖ ^ 2 else 0 with hS2
  have e1 : ‖Mc σ 1 u‖ ^ 2 = S1 + S2 := by
    rw [EuclideanSpace.norm_sq_eq, hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ']
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ]
      · simp [Mc_apply, h1, h2]
  have e2 : ‖prj σ u‖ ^ 2 = S1 := by
    rw [EuclideanSpace.norm_sq_eq, hS1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1 = σ <;> simp [prj_apply, h1]
  have e3 : (Hf (Mc σ 1 u) (Mc σ Complex.I u)).im = S2 - S1 := by
    rw [Hf, Complex.im_sum, hS1, hS2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ', Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
      · simp [Mc_apply, h1, h2]
  have e4 := Hf_im_IR_lemma hI h1 hi
  linarith

lemma orth_prj [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) {t y : Vsp dim} (ht : t ∈ IR I)
    (hy : ∀ c, Mc σ c y ∈ IR I) (horth : ∀ c, inner ℝ t (Mc σ c y) = 0) :
    Hf (prj σ t) (prj σ y) = 0 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  have hre : ∀ a : Vsp dim, inner ℝ t a = (Hf t a).re := by
    intro a
    rw [PiLp.inner_apply, Hf, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, Complex.mul_re]
    ring
  have key : ∀ c : ℂ, Hf t (Mc σ c y) = (starRingEnd ℂ) c * Hf (prj σ t) (prj σ y) +
      c * Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y) := by
    intro c
    rw [Hf, Hf, Hf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, prj_apply, h1, hσ'] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, prj_apply, h1, h2, hσ] <;> ring
      · simp [Mc_apply, prj_apply, h1, h2]
  have hz : ∀ c : ℂ, Hf t (Mc σ c y) = 0 := fun c =>
    Complex.ext (by rw [← hre]; simpa using horth c) (by simpa using Hf_im_IR_lemma hI ht (hy c))
  have e1 := (key 1).symm.trans (hz 1)
  have e2 := (key Complex.I).symm.trans (hz Complex.I)
  rw [map_one] at e1
  rw [Complex.conj_I] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 +
    ((Hf (prj σ t) (prj σ y) - Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y)) / 2) *
      Complex.I_sq

abbrev conjO [IsCMField E] (α : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E α

lemma emb_conjO [IsCMField E] (α : 𝓞 E) (τ : E →+* ℂ) :
    τ ((conjO α : 𝓞 E) : E) = (starRingEnd ℂ) (τ (α : E)) := by
  simp [conjO, NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexEmbedding_complexConj]

lemma act_apply {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) :
    act α v i = i.1 (α : E) * v i := rfl

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun := act α
  map_add' v w := by ext i; simp only [act_apply, PiLp.add_apply]; ring
  map_smul' c v := by ext i; simp only [act_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma act_add_left {dim : (E →+* ℂ) → ℕ} (α β : 𝓞 E) (v : Vsp dim) :
    act (α + β) v = act α v + act β v := by
  ext i
  simp [act, add_mul]

lemma Hf_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x a : Vsp dim) :
    Hf (act α x) a = Hf x (act (conjO α) a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO]
  ring

lemma inner_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (u a : Vsp dim) :
    inner ℝ (act α u) a = inner ℝ u (act (conjO α) a) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

lemma act_mem_IR {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {a : Vsp dim} (ha : a ∈ IR I) :
    act α a ∈ IR I := by
  have key : Submodule.span ℝ (I : Set (Vsp dim)) ≤ (IR I).comap ((actL α).restrictScalars ℝ) := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span (hs α x hx)
  exact key ha

lemma isU_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {x u : Vsp dim} (h : IsU I x u) :
    IsU I (act α x) (act α u) := by
  exact ⟨act_mem_IR hs α h.1, fun a ha => by
    rw [inner_act, h.2 _ (act_mem_IR hs _ ha), Hf_act]⟩

lemma norm_act_le {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (B : ℝ) (hB : ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ B)
    (v : Vsp dim) : ‖act α v‖ ≤ B * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv
    rw [show act α (0 : Vsp dim) = 0 from (actL α).map_zero]
    simp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (by ext i; simpa using h i)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i.1)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hB0, ← Real.sqrt_mul (sq_nonneg B)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [act, PiLp.toLp_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB j.1) 2) (sq_nonneg _)

def Xg {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) : AddSubgroup (Vsp dim) where
  carrier := {u | ∃ x ∈ L, IsU I x u}
  add_mem' := by
    rintro u v ⟨x, hx, hu⟩ ⟨y, hy, hv⟩; exact ⟨x + y, L.add_mem hx hy, isU_add hu hv⟩
  zero_mem' := ⟨0, L.zero_mem, isU_zero I⟩
  neg_mem' := by rintro u ⟨x, hx, hu⟩; exact ⟨-x, L.neg_mem hx, isU_neg hu⟩

lemma Xg_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hL : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (α : 𝓞 E) {u : Vsp dim} (hu : u ∈ Xg L I) : act α u ∈ Xg L I := by
  obtain ⟨x, hx, h⟩ := hu
  exact ⟨act α x, hL α x hx, isU_act hs α h⟩

lemma Xg_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)} {u : Vsp dim}
    (hu : u ∈ Xg L I) : u ∈ IR I := by
  obtain ⟨x, -, h⟩ := hu
  exact h.1

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
