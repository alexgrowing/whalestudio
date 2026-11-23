import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurePreservingSwapPi

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module NumberField Set

set_option backward.isDefEq.respectTransparency.types false in
theorem covol_div_covol_eq_relIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  let e : Module.Free.ChooseBasisIndex ℤ L₁ ≃ Module.Free.ChooseBasisIndex ℤ L₂ :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂])
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex e
  let b₀ := b₂.ofZLatticeBasis ℝ L₂
  have h1 := ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ b₀
  have h2 := ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ b₀
  have hb : ((↑) ∘ b₂ : _ → E) = ⇑b₀ := by ext i; simp [b₀, Basis.ofZLatticeBasis_apply]
  rw [hb, Basis.det_self, abs_one, one_mul] at h2
  have hpos := ZLattice.covolume_pos L₂ μ
  rw [h2] at hpos
  rw [h1, h2, mul_div_assoc, div_self hpos.ne', mul_one,
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (Submodule.coe_mem _)⟩ i)

theorem measurePreserving_swapPi {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) => f i k)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => Measure.pi fun _ : ι => ν) := by
  first | exact UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi .. | (apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> first | assumption | infer_instance)

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open Matrix

section Form

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.form_add_left (h : HermFam K V) (σ : K →+* ℂ) (x x' y : V) :
    h.form σ (x + x') y = h.form σ x y + h.form σ x' y := by
  rw [← h.conj_symm, h.add_right, map_add, h.conj_symm, h.conj_symm]

theorem HermFam.form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

theorem HermFam.form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, h.form_sum_right, map_sum]
  simp only [h.conj_symm]

theorem HermFam.form_expand (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (c : Fin n → K)
    (v : Fin n → V) :
    h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.gram σ v i j * σ (c j) := by
  rw [h.form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.form_smul_left, h.smul_right, HermFam.gram, Matrix.of_apply]
  ring

end Form

section Places

variable {K : Type*} [Field K] [NumberField K]

end Places

end ReciprocityTheory.GeometryOfNumbersTheory
