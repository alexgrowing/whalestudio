import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_one {i : A.ι} {v : V n} (hv : v ∈ (A.e i).target) : A.loc 1 i v = 1 := by
  rw [HolAtlas.loc, dif_pos hv]; rfl

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, dif_neg hv, add_zero]

theorem loc_mul (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, dif_neg hv, mul_zero]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, smul_zero]

theorem isForm_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  intro M _ n A
  refine ⟨⟨fun i S => ?_, fun x x' _ => ?_⟩, fun c α β hα hβ => ⟨⟨fun i S => ?_, fun x x' h => ?_⟩,
    ⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩⟩
  · exact (contDiffOn_const (c := (bas n).repr (1 : Alt n) S)).congr fun v hv => by
      rw [loc_one A hv]
  · exact (map_one _).symm
  · exact ((hα.smooth i S).add (hβ.smooth i S)).congr fun v _ => by
      rw [loc_add, map_add, Finsupp.add_apply]
  · change α x + β x = pull _ (α x' + β x')
    rw [map_add, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_complexForm_mul n n (A.loc α i) (A.loc β i)).1 _ (hα.smooth i) (hβ.smooth i) S).congr fun v _ => by
      rw [loc_mul]
  · change α x * β x = pull _ (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((hα.smooth i S).const_smul c).congr fun v _ => by
      rw [loc_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · change c • α x = pull _ (c • α x')
    rw [map_smul, ← hα.compat x x' h]

end GlobalTheory.CxForm.HolAtlas
