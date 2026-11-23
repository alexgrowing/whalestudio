import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActOmegaExpand

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Zs {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ {x | ∃ α : 𝓞 E, ∃ y ∈ Xg L I, ‖y‖ ≤ μ ∧ x = act α y}

lemma Zs_mono {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ μ' : ℝ} (h : μ ≤ μ') :
    Zs L I μ ≤ Zs L I μ' := Submodule.span_mono fun _ ⟨α, y, hy, hyμ, hx⟩ => ⟨α, y, hy, hyμ.trans h, hx⟩

lemma Zs_self {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ : ℝ} {y : Vsp dim}
    (hy : y ∈ Xg L I) (hμ : ‖y‖ ≤ μ) : y ∈ Zs L I μ := by
  refine Submodule.subset_span ⟨1, y, hy, hμ, ?_⟩
  ext i
  simp [act]

private lemma act_add_lemma {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (x y : Vsp dim) :
    act β (x + y) = act β x + act β y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_smul_lemma_2 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (r : ℝ) (x : Vsp dim) :
    act β (r • x) = r • act β x := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_zero_lemma_4 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) : act β (0 : Vsp dim) = 0 := by
  ext i
  simp [act]

private lemma act_mul_lemma_5 {dim : (E →+* ℂ) → ℕ} (β α : 𝓞 E) (y : Vsp dim) :
    act β (act α y) = act (β * α) y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_span_lemma_3 {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim)) (β : 𝓞 E)
    (hS : ∀ y ∈ S, act β y ∈ Submodule.span ℝ S) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act β a ∈ Submodule.span ℝ S := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [act_zero_lemma_4]; exact zero_mem _
  | add x y _ _ hx hy => rw [act_add_lemma]; exact add_mem hx hy
  | smul r x _ hx => rw [act_smul_lemma_2]; exact Submodule.smul_mem _ r hx

lemma Zs_act {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) (β : 𝓞 E)
    {x : Vsp dim} (hx : x ∈ Zs L I μ) : act β x ∈ Zs L I μ := by
  refine act_span_lemma_3 _ β ?_ hx
  rintro _ ⟨α, y, hy, hyμ, rfl⟩
  exact Submodule.subset_span ⟨β * α, y, hy, hyμ, act_mul_lemma_5 β α y⟩

lemma Zs_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (μ : ℝ) : Zs L I μ ≤ IR I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, y, hy, -, rfl⟩
  obtain ⟨x, -, hu⟩ : ∃ x ∈ L, IsU I x y := hy
  exact act_span_lemma_3 _ α (fun z hz => Submodule.subset_span (hIs α z hz)) hu.1

lemma prj_rsmul {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Vsp dim) :
    prj σ (r • x) = r • prj σ x := by
  simp only [prj]
  exact LinearMap.map_smul_of_tower _ r x

private lemma prj_add_lemma_6 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (x y : Vsp dim) :
    prj σ (x + y) = prj σ x + prj σ y := by
  simp only [prj]
  exact map_add _ x y

private lemma prj_zero_lemma_7 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : prj σ (0 : Vsp dim) = 0 := by
  simp only [prj]
  exact map_zero _

lemma prj_mem_of_span {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (S : Set (Vsp dim)) (hS : ∀ y ∈ S, prj σ y ∈ W) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : prj σ a ∈ W := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [prj_zero_lemma_7]; exact zero_mem _
  | add x y _ _ hx hy => rw [prj_add_lemma_6]; exact add_mem hx hy
  | smul r x _ hx => rw [prj_rsmul]; exact W.smul_of_tower_mem r hx

lemma span_act {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim))
    (hS : ∀ (α : 𝓞 E) y, y ∈ S → act α y ∈ S) (α : 𝓞 E) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act α a ∈ Submodule.span ℝ S := act_span_lemma_3 S α (fun y hy => Submodule.subset_span (hS α y hy)) ha

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
