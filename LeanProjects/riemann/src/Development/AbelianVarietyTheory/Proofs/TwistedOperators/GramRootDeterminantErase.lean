import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootDecomposeOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramDetOptionFormulaStatement
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

def optInsertEquiv {α : Type} [DecidableEq α] (u : α) (s : Finset α) (hu : u ∉ s) :
    Option ↥s ≃ ↥(insert u s) where
  toFun o := o.elim ⟨u, Finset.mem_insert_self u s⟩ fun v => ⟨v.1, Finset.mem_insert_of_mem v.2⟩
  invFun w := if h : w.1 = u then none else some ⟨w.1, (Finset.mem_insert.mp w.2).resolve_left h⟩
  left_inv o := by
    cases o with
    | none => simp
    | some v =>
      have : v.1 ≠ u := fun h => hu (h ▸ v.2)
      simp [this]
  right_inv w := by
    by_cases h : w.1 = u
    · simp only [h, dite_true, Option.elim]; exact Subtype.ext h.symm
    · simp only [h, dite_false, Option.elim]

theorem gram_det_reindex {k : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (f : ι → A0 k) : (Matrix.gram ℝ (f ∘ e)).det = (Matrix.gram ℝ f).det := by
  have : Matrix.gram ℝ (f ∘ e) = (Matrix.gram ℝ f).submatrix e e := by
    ext i j; simp [Matrix.gram]
  rw [this, Matrix.det_submatrix_equiv_self]

end GlobalTheory.Chamber

namespace GlobalTheory.Chamber

theorem rt_residue_identity : ∀ {k : ℕ} {T : Finset (SV k)} {u : SV k} (s : Finset (SV k)), IsPar T → u ∈ T → s ⊆ T.erase u →
  ∀ x : A0 k, ⟪x, rt T u⟫_ℝ = 0 →
  √(Matrix.gram ℝ fun v : ↥(insert u s) => rt T v).det * ∏ v ∈ s, (⟪x, rt T v⟫_ℝ)⁻¹ =
    ‖rt T u‖ * √(Matrix.gram ℝ fun v : ↥s => rt (T.erase u) v).det * ∏ v ∈ s, (⟪x, rt (T.erase u) v⟫_ℝ)⁻¹ := by
  intro k T u s hT hu hs x hx
  have hmem : ∀ v ∈ s, v ∈ T ∧ v ≠ u := fun v hv => by
    have := hs hv; rw [Finset.mem_erase] at this; exact ⟨this.2, this.1⟩
  have hus : u ∉ s := fun h => (hmem u h).2 rfl

  have hex : ∀ v, ∃ κ : ℝ, 0 < κ ∧ ∃ t : ℝ, (v ∈ T ∧ v ≠ u →
      rt T v = κ • rt (T.erase u) v + t • rt T u ∧ ⟪rt (T.erase u) v, rt T u⟫_ℝ = 0) := by
    intro v
    by_cases h : v ∈ T ∧ v ≠ u
    · obtain ⟨κ, hκ, t, h1, h2⟩ := GlobalTheory.T.root_decompose_orthogonal hT hu h.1 h.2
      exact ⟨κ, hκ, t, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, one_pos, 0, fun h' => absurd h' h⟩
  choose κ hκ t ht using hex
  set S := T.erase u
  set w0 := rt T u
  have hrt : ∀ v ∈ s, rt T v = κ v • rt S v + t v • w0 := fun v hv => (ht v (hmem v hv)).1
  have horth : ∀ v ∈ s, ⟪rt S v, w0⟫_ℝ = 0 := fun v hv => (ht v (hmem v hv)).2

  have hdet : (Matrix.gram ℝ fun v : ↥(insert u s) => rt T v).det =
      ‖w0‖ ^ 2 * (∏ v ∈ s, κ v ^ 2) * (Matrix.gram ℝ fun v : ↥s => rt S v).det := by
    rw [← gram_det_reindex (optInsertEquiv u s hus) (fun v : ↥(insert u s) => rt T v)]
    have hf : ((fun v : ↥(insert u s) => rt T v) ∘ optInsertEquiv u s hus) =
        fun o : Option ↥s => o.elim w0 fun i => κ i • rt S i + t i • w0 := by
      funext o
      cases o with
      | none => rfl
      | some v => exact hrt v.1 v.2
    rw [hf, GlobalTheory.T.gram_det_option_formula w0 (fun i : ↥s => rt S i) (fun i => κ i) (fun i => t i) (fun i => horth i.1 i.2),
      Finset.prod_coe_sort s (fun v => κ v ^ 2)]
  have hκpos : 0 < ∏ v ∈ s, κ v := Finset.prod_pos fun v _ => hκ v
  have hsq : √(Matrix.gram ℝ fun v : ↥(insert u s) => rt T v).det =
      ‖w0‖ * (∏ v ∈ s, κ v) * √(Matrix.gram ℝ fun v : ↥s => rt S v).det := by
    rw [hdet, show ‖w0‖ ^ 2 * (∏ v ∈ s, κ v ^ 2) = (‖w0‖ * ∏ v ∈ s, κ v) ^ 2 by
      rw [mul_pow, Finset.prod_pow], Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

  have hinner : ∀ v ∈ s, ⟪x, rt T v⟫_ℝ = κ v * ⟪x, rt S v⟫_ℝ := by
    intro v hv
    rw [hrt v hv, inner_add_right, inner_smul_right, inner_smul_right, hx, mul_zero, add_zero]
  have hprod : ∏ v ∈ s, (⟪x, rt T v⟫_ℝ)⁻¹ = (∏ v ∈ s, κ v)⁻¹ * ∏ v ∈ s, (⟪x, rt S v⟫_ℝ)⁻¹ := by
    rw [Finset.prod_congr rfl fun v hv => by rw [hinner v hv, mul_inv], Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
  rw [hsq, hprod]
  have : (∏ v ∈ s, κ v) ≠ 0 := hκpos.ne'
  field_simp

end GlobalTheory.Chamber
