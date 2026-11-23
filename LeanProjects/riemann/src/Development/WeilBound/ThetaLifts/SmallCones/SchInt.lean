import Mathlib
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq

noncomputable section

namespace PositivityTheory.ThKCT

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _) ?_
  refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
  have := (jet k j f).norm_coe_le_norm x
  rwa [jet_apply, norm_smul, norm_pow, norm_norm] at this

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

theorem J_apply (k j : ℕ) (f : SchwartzMap V ℂ) : J k j f = jet k j f := rfl

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ :=
  (hI k j).mono' ((J k j).continuous.comp hG).aestronglyMeasurable (.of_forall fun a => (norm_jet k j _).le)

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp ((J 0 j).continuous.comp hG)
  refine this.congr fun a => ?_
  change jet 0 j (G a) x = _
  rw [jet_apply, pow_zero, one_smul]

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  simpa using SchwartzMap.le_seminorm ℂ 0 j f x

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ :=
  (hI 0 j).mono' (cont_D hG j x).aestronglyMeasurable (.of_forall fun a => bd_D _ j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ) (x₀ := x)
    (F := fun y a => iteratedFDeriv ℝ j (G a) y) (F' := fun y a => L (iteratedFDeriv ℝ (j + 1) (G a) y))
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) univ_mem
    (.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x)
    (L.continuous.comp (cont_D hG (j + 1) x)).aestronglyMeasurable
    (.of_forall fun a y _ => by rw [L.norm_map]; exact bd_D _ _ y) (hI 0 (j + 1))
    (.of_forall fun a y _ => ((cd (G a) (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) y).hasFDerivAt)
  have e := L.toContinuousLinearEquiv.integral_comp_comm (μ := μ) fun a => iteratedFDeriv ℝ (j + 1) (G a) x
  exact h.congr_fderiv e

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ where
  zero_eq x := ((continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.integral_comp_comm (μ := μ)
    fun a => iteratedFDeriv ℝ 0 (G a) x).symm
  fderiv j _ x := deriv_D hG hI j x
  cont j _ := continuous_iff_continuousAt.2 fun x => (deriv_D hG hI j x).continuousAt

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  rw [← (taylor hG hI).eq_iteratedFDeriv (by exact_mod_cast le_top) x, ← integral_smul]
  exact ((BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm (int_J hG hI k j)).symm

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k j => ⟨‖∫ a, J k j (G a) ∂μ‖, fun x => ?_⟩⟩, fun k j => ?_⟩
  · have := (∫ a, J k j (G a) ∂μ).norm_coe_le_norm x
    rwa [eval_int hG hI, norm_smul, norm_pow, norm_norm] at this
  · ext1 x
    rw [eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let j : SchwartzMap V ℂ →ₗ[ℂ] ∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ) := LinearMap.pi fun i => (J i.1.1 i.1.2).toLinearMap
  have hb : ∀ f, ‖T f‖ ≤ C * ‖j f‖ := fun f => by
    refine (h f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_jet i.1 i.2 f).ge.trans (norm_le_pi_norm (j f) ⟨i, hi⟩)
  have hk : LinearMap.ker j ≤ LinearMap.ker T.toLinearMap := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let t : LinearMap.range j →ₗ[ℂ] ℂ := ((LinearMap.ker j).liftQ T.toLinearMap hk) ∘ₗ j.quotKerEquivRange.symm.toLinearMap
  have ht : ∀ f, t ⟨j f, f, rfl⟩ = T f := fun f => by
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [j.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (t.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [ht]
    exact hb f))
  exact ⟨s, g, fun f => ((hg ⟨j f, f, rfl⟩).trans (ht f)).symm⟩

end SchI

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
