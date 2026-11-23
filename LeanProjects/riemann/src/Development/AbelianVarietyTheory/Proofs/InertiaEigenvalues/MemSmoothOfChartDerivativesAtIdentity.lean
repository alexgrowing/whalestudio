import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ContDiff

namespace GlobalTheory.SmOfDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def compLmul (ℓ : Lie E a →L[ℝ] ℂ) : Lie E a →L[ℝ] (Lie E a →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ℓ.comp (lmul M)
      map_add' := fun M N => by
        ext v
        change ℓ (toL ((Matrix.of M + Matrix.of N) * Matrix.of v)) = ℓ (toL (Matrix.of M * Matrix.of v)) + ℓ (toL (Matrix.of N * Matrix.of v))
        rw [Matrix.add_mul]
        exact map_add ℓ (toL (Matrix.of M * Matrix.of v)) (toL (Matrix.of N * Matrix.of v))
      map_smul' := fun c M => by
        ext v
        change ℓ (toL ((c • Matrix.of M) * Matrix.of v)) = c • ℓ (toL (Matrix.of M * Matrix.of v))
        rw [Matrix.smul_mul]
        exact map_smul ℓ c (toL (Matrix.of M * Matrix.of v)) }

theorem contDiffAt_inv {z : Lie E a} (hz : z ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) z := by
  have hdet : IsUnit (Matrix.of z).det := (Matrix.isUnit_iff_isUnit_det _).1 hz
  have h1 : ContDiffAt ℝ ∞ (fun x : Lie E a => Ring.inverse (Matrix.of x).det) z := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) hdet.unit
    rw [IsUnit.unit_spec] at h
    exact h.comp z (contDiff_det (E := E)).contDiffAt
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun x : Lie E a => Matrix.adjugate (Matrix.of x) i j := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ _ k).comp (contDiff_apply ℝ _ (σ k))
  have e : (fun x : Lie E a => toL (Matrix.of x)⁻¹ i j) =
      fun x => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x
    rw [Matrix.inv_def]
    rfl
  rw [e]
  exact h1.mul h2.contDiffAt

theorem hasFDerivAt_chart {f : GA E a → ℂ} {ι : Type} [Fintype ι] {fs : ι → GA E a → ℂ}
    {ℓ : ι → (Lie E a →L[ℝ] ℂ)} (hd : ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a))
    (g : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart f g) (∑ i, chart (fs i) g z • compLmul (ℓ i) (toL (Matrix.of z)⁻¹)) z := by
  obtain ⟨y, hy⟩ := hz
  obtain rfl : z = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  have h := hd (g * infGL E a y)
  rw [← e1] at h
  have h2 := h.comp (toL y.val) (lmul (toL (y⁻¹).val)).hasFDerivAt
  rw [← e] at h2
  refine h2.congr_fderiv ?_
  have ei : toL (Matrix.of (toL y.val))⁻¹ = toL (y⁻¹).val := by
    change toL (y.val)⁻¹ = toL (y⁻¹).val
    rw [Matrix.coe_units_inv]
  rw [ei]
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chart_val]
  rfl

theorem mem_Sm_of_hasFDerivAt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  intro E _ _ _ a K hK
  have key : ∀ n : ℕ, ∀ f ∈ K, ∀ g, ∀ z ∈ invSet E a, ContDiffAt ℝ n (chart f g) z := by
    intro n
    induction n with
    | zero =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, -, hd⟩ := hK f hf
      exact contDiffAt_zero.2 ⟨invSet E a, isOpen_invSet.mem_nhds hz, fun x hx =>
        (hasFDerivAt_chart hd g hx).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, hfs, hd⟩ := hK f hf
      rw [Nat.cast_succ]
      refine contDiffAt_succ_iff_hasFDerivAt.2 ⟨_, ⟨invSet E a, isOpen_invSet.mem_nhds hz,
        fun x hx => hasFDerivAt_chart hd g hx⟩, ?_⟩
      refine ContDiffAt.sum fun i _ => (ih (fs i) (hfs i) g z hz).smul ?_
      exact (compLmul (ℓ i)).contDiff.contDiffAt.comp z (contDiffAt_infty.1 (contDiffAt_inv hz) n)
  intro f hf g z hz
  exact (contDiffAt_infty.2 fun n => key n f hf g z hz).contDiffWithinAt

end GlobalTheory.SmOfDeriv
