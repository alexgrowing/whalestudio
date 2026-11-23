import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.PoissonV

variable (ι κ : Type) [Fintype ι] [Fintype κ]

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in

theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : MeasurePreserving (MeasurableEquiv.curry ι κ ℂ).symm volume volume := by
    refine ⟨(MeasurableEquiv.curry ι κ ℂ).symm.measurable, ?_⟩
    have hv : (volume : Measure (ι × κ → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [hv]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
      ext x
      simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using h.symm

def coords : EuclideanSpace ℂ (ι × κ) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a => x (w, a)
      invFun := fun y => WithLp.toLp 2 fun p => y p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem coords_apply (x : EuclideanSpace ℂ (ι × κ)) (w : ι) (a : κ) : coords ι κ x w a = x (w, a) := rfl

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords :
    MeasurePreserving (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ) volume volume :=
  (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry ι κ).comp (_root_.GlobalTheory.volume_preserving_ofLp_complex _)

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords (x : EuclideanSpace ℂ (ι × κ)) :
    ∑ w, ∑ a, ‖_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ x w a‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem inner_coords (x y : EuclideanSpace ℂ (ι × κ)) :
    ∑ w, (coords ι κ x w ⬝ᵥ star (coords ι κ y w)).re = inner ℝ x y := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [coords_apply, Complex.inner]
  ring

end GlobalTheory.FlagBase.PoissonV

namespace GlobalTheory.FlagBase

open PoissonV

theorem mem_dualAt (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j))
    (y : VecInf E j) : y ∈ dualAt E j L ↔ ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact fun x _ => ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    intro x hx
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by simp [dotProduct_add, Finset.sum_add_distrib, hm, hn]⟩
  | smul c a _ ha =>
    intro x hx
    obtain ⟨m, hm⟩ := ha x hx
    refine ⟨c * m, ?_⟩
    rw [Int.cast_mul, ← hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pi.smul_apply, dotProduct_smul]
    simp

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
private theorem inner_toLp_conj_eq_sum_re_dotProduct (u : EuclideanSpace ℂ (ι × κ))
    (y : ι → κ → ℂ) :
    inner ℝ u (WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2) : EuclideanSpace ℂ (ι × κ)) =
      ∑ w, (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ u w ⬝ᵥ y w).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [_root_.GlobalTheory.FlagBase.PoissonV.coords, dotProduct, Complex.re_sum, Complex.mul_re]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => mul_comm _ _

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.FlagBase.poisson_gaussV (E : Type) [Field E] [NumberField E] (j : ℕ)
    (L : Submodule ℤ (_root_.GlobalTheory.FlagBase.VecInf E j))
    [DiscreteTopology L] (hL : IsZLattice ℝ L) :
    Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) ∧
      Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) ∧
      ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x =
        (_root_.GlobalTheory.FlagBase.covAt E j L)⁻¹ *
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y ∧
      ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = 1 := by
  classical
  haveI := hL
  let e := _root_.GlobalTheory.FlagBase.PoissonV.coords (InfinitePlace E) (Fin j)
  let L' := ZLattice.comap ℝ L
    (e : EuclideanSpace ℂ (InfinitePlace E × Fin j) →ₗ[ℝ] _root_.GlobalTheory.FlagBase.VecInf E j)
  have hmemL : ∀ u, u ∈ L' ↔ e u ∈ L := fun u => Iff.rfl
  have hg : ∀ u, _root_.GlobalTheory.FlagBase.gaussV E j (e u) = Real.exp (-Real.pi * ‖u‖ ^ 2) := by
    intro u
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖e u w a‖ ^ 2) = _
    rw [_root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords]
  have hg' : ∀ x, _root_.GlobalTheory.FlagBase.gaussV E j x = Real.exp (-Real.pi * ‖e.symm x‖ ^ 2) := by
    intro x
    rw [← hg, ContinuousLinearEquiv.apply_symm_apply]
  let eL : L ≃ L' :=
    { toFun := fun y => ⟨e.symm y, by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact y.2⟩
      invFun := fun x => ⟨e x, (hmemL x).1 x.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  let ψ : _root_.GlobalTheory.FlagBase.VecInf E j ≃ EuclideanSpace ℂ (InfinitePlace E × Fin j) :=
    { toFun := fun y => WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2)
      invFun := fun z w a => starRingEnd ℂ (z (w, a))
      left_inv := fun y => by funext w a; simp
      right_inv := fun z => by ext p; simp }
  have hψ : ∀ y, _root_.GlobalTheory.FlagBase.gaussV E j y = Real.exp (-Real.pi * ‖ψ y‖ ^ 2) := by
    intro y
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖y w a‖ ^ 2) = _
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [ψ]
  have hinner : ∀ u y, inner ℝ u (ψ y) = ∑ w, (e u w ⬝ᵥ y w).re :=
    fun u y => inner_toLp_conj_eq_sum_re_dotProduct _ _ u y
  have hdual : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔
      ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
    intro y
    unfold _root_.GlobalTheory.FlagBase.dualAt
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => intro x _; exact ⟨0, by simp⟩
      | add y y' _ _ h h' =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        obtain ⟨z', hz'⟩ := h' x hx
        refine ⟨z + z', ?_⟩
        simp only [Pi.add_apply, dotProduct_add, Complex.add_re, Finset.sum_add_distrib, hz, hz']
        push_cast
        ring
      | smul n y _ h =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        refine ⟨n * z, ?_⟩
        simp only [Pi.smul_apply, dotProduct_smul, Complex.smul_re]
        rw [← Finset.smul_sum, hz, zsmul_eq_mul]
        push_cast
        ring
    · intro hy
      exact Submodule.subset_span hy
  have hmem : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔ ψ y ∈ _root_.GlobalTheory.dualLattice L' := by
    intro y
    rw [hdual, _root_.GlobalTheory.mem_dualLattice]
    constructor
    · intro h u hu
      obtain ⟨z, hz⟩ := h (e u) ((hmemL u).1 hu)
      exact ⟨z, by rw [hinner, hz]⟩
    · intro h x hx
      obtain ⟨m, hm⟩ := h (e.symm x) (by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact hx)
      refine ⟨m, ?_⟩
      rw [hm, hinner, ContinuousLinearEquiv.apply_symm_apply]
  let dL : _root_.GlobalTheory.FlagBase.dualAt E j L ≃ _root_.GlobalTheory.dualLattice L' := ψ.subtypeEquiv hmem
  let f : EuclideanSpace ℂ (InfinitePlace E × Fin j) → ℝ := fun u => Real.exp (-Real.pi * ‖u‖ ^ 2)
  have hsL : Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) :=
    ((eL.summable_iff (f := fun x : L' => f x)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L' Real.pi_pos)).congr fun x => by rw [hg']; rfl
  have hsD : Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) :=
    ((dL.summable_iff (f := fun z : _root_.GlobalTheory.dualLattice L' => f z)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq _ Real.pi_pos)).congr fun y => by rw [hψ]; rfl
  have hT1 : ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L', f x :=
    calc ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L, f (eL x) :=
          tsum_congr fun x => by rw [hg']; rfl
      _ = ∑' x : L', f x := eL.tsum_eq (fun x : L' => f x)
  have hT2 : ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
      ∑' z : _root_.GlobalTheory.dualLattice L', f z :=
    calc ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, f (dL y) :=
          tsum_congr fun y => by rw [hψ]; rfl
      _ = ∑' z : _root_.GlobalTheory.dualLattice L', f z := dL.tsum_eq (fun z : _root_.GlobalTheory.dualLattice L' => f z)
  haveI : (volume : Measure (_root_.GlobalTheory.FlagBase.VecInf E j)).IsAddHaarMeasure := by
    rw [← (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).map_eq]
    exact e.isAddHaarMeasure_map volume
  have hcov : _root_.GlobalTheory.FlagBase.covAt E j L = ZLattice.covolume L' volume := by
    show ZLattice.covolume L volume = _
    exact (ZLattice.covolume_comap L volume volume
      (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords _ _)).symm
  have hP := _root_.GlobalTheory.tsum_gaussian_lattice_eq_dualLattice L' one_pos
  simp only [mul_one, Real.one_rpow, div_one] at hP
  refine ⟨hsL, hsD, ?_, ?_⟩
  · rw [hT1, hT2, hcov]
    exact hP
  · have hI : ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = ∫ u, f u :=
      ((_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).integral_comp
        e.toHomeomorph.measurableEmbedding (_root_.GlobalTheory.FlagBase.gaussV E j)).symm.trans
        (integral_congr_ae (Filter.Eventually.of_forall fun u => hg u))
    rw [hI]
    show ∫ u, Real.exp (-Real.pi * ‖u‖ ^ 2) = 1
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm Real.pi_pos, div_self Real.pi_ne_zero,
      Real.one_rpow]

end GlobalTheory.FlagBase
