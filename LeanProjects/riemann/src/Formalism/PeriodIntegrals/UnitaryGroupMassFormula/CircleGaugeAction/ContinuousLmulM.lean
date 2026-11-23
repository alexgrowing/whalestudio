import Mathlib
import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.DglApplyOff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.OfRealCoordsSmulCenterCoord

noncomputable section

open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

instance fact_two_pi : Fact (0 < 2 * π) := ⟨by positivity⟩

def Gm (r : ℕ) (θ : AddCircle (2 * π)) : Mt 0 r :=
  fun i j => dgl r ((AddCircle.toCircle θ : Circle) : ℂ) i j

lemma toCircle_coe (s : ℝ) :
    ((AddCircle.toCircle (s : AddCircle (2 * π)) : Circle) : ℂ) = Complex.exp (s * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, div_self (ne_of_gt fact_two_pi.out), one_mul, Circle.coe_exp]

lemma continuous_Gm : Continuous (Gm r) := by
  have hc : Continuous fun θ : AddCircle (2 * π) => ((AddCircle.toCircle θ : Circle) : ℂ) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Gm, dgl_apply]
  split_ifs
  · exact hc
  · exact continuous_const
  · exact continuous_const

lemma Gm_injective : Function.Injective (Gm r) := by
  intro a b h
  have := congrFun (congrFun h (cI r)) (cI r)
  simp only [Gm, dgl_apply] at this
  exact AddCircle.injective_toCircle (ne_of_gt fact_two_pi.out) (Circle.ext this)

lemma me_Gm : MeasurableEmbedding (Gm r) :=
  (continuous_Gm.isClosedEmbedding Gm_injective).measurableEmbedding

lemma Gm_mem (θ : AddCircle (2 * π)) : Matrix.of (Gm r θ) ∈ UWb 0 r := by
  show dgl r _ ∈ UWb 0 r
  exact dgl_mem ((conj_mul_iff _).2 (Circle.norm_coe _))

lemma continuous_lmulM (a : Mat 0 r) : Continuous (lmulM (k := 0) (r := r) a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, mul_apply, of_apply]
  exact continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

lemma Gm_add (a b : AddCircle (2 * π)) :
    Gm r (a + b) = lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) := by
  have : lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) =
      dgl r ((AddCircle.toCircle a : Circle) : ℂ) * dgl r ((AddCircle.toCircle b : Circle) : ℂ) := rfl
  have h2 : ((AddCircle.toCircle (a + b) : Circle) : ℂ) =
      ((AddCircle.toCircle a : Circle) : ℂ) * ((AddCircle.toCircle b : Circle) : ℂ) := by
    rw [AddCircle.toCircle_add, Circle.coe_mul]
  rw [this, dgl_mul]
  unfold Gm
  rw [h2]

def μG (r : ℕ) : Measure (Mt 0 r) := Measure.map (Gm r) volume

lemma map_lmul (s : Mat 0 r) (hs : s ∈ UWb 0 r) : (μG r).map (lmulM s) = μG r := by
  obtain ⟨u, hu, rfl⟩ := (mem_UWb_iff s).1 hs
  rw [conj_mul_iff] at hu
  have hα : ((AddCircle.toCircle ((Complex.arg u : ℝ) : AddCircle (2 * π)) : Circle) : ℂ) = u := by
    rw [toCircle_coe]
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hu] at this
    simpa using this
  unfold μG
  rw [Measure.map_map (continuous_lmulM _).measurable continuous_Gm.measurable]
  have hcomp : lmulM (dgl r u) ∘ Gm r =
      Gm r ∘ (fun θ => ((Complex.arg u : ℝ) : AddCircle (2 * π)) + θ) := by
    funext θ
    simp only [Function.comp_apply]
    rw [Gm_add, hα]
  rw [hcomp, ← Measure.map_map continuous_Gm.measurable (measurable_const_add _),
    map_add_left_eq_self]

lemma isHaar : IsHaarOn (UWb 0 r) (μG r) := by
  refine ⟨?_, ?_, ?_, fun s hs => map_lmul s hs⟩
  · unfold μG; infer_instance
  · unfold μG
    rw [Ne, Measure.map_eq_zero_iff continuous_Gm.measurable.aemeasurable]
    intro h
    have h1 := AddCircle.measure_univ (2 * π)
    rw [h, Measure.coe_zero, Pi.zero_apply, eq_comm, ENNReal.ofReal_eq_zero] at h1
    linarith [Real.pi_pos]
  · unfold μG
    rw [me_Gm.map_apply]
    have : Gm r ⁻¹' {x | Matrix.of x ∉ UWb 0 r} = ∅ := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Gm_mem θ
    rw [this, measure_empty]

lemma expBall_eq (ρ : ℝ) :
    expBall (UWb 0 r) ρ = Gm r '' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x.1 ∈ Submodule.span ℝ {v0 r} := by
      rw [← lieE_eq]; exact x.2
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hx'
    have hn : ‖x.1‖ = |s| := by
      rw [← hs, norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs]
    have hlt : |s| < ρ := by
      rw [← hn]; exact mem_ball_zero_iff.1 hx
    refine ⟨(s : AddCircle (2 * π)), ⟨s, abs_lt.1 hlt, rfl⟩, ?_⟩
    show Gm r s = fun i j => NormedSpace.exp (unrealify x.1) i j
    rw [← hs, ofRealCoords_smul_centerCoord, exp_dz]
    unfold Gm
    rw [toCircle_coe]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hmem : s • v0 r ∈ lieE (UWb 0 r) := by
      rw [lieE_eq]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    refine ⟨⟨s • v0 r, hmem⟩, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      show ‖s • v0 r‖ < ρ
      rw [norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs, abs_lt]
      exact hs
    · show (fun i j => NormedSpace.exp (unrealify (s • v0 r)) i j) = Gm r s
      rw [ofRealCoords_smul_centerCoord, exp_dz]
      unfold Gm
      rw [toCircle_coe]

lemma vol_arc {ρ : ℝ} (hρ : ρ ≤ π) :
    volume (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by
  have hopen : IsOpen (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  rw [AddCircle.add_projection_respects_measure (2 * π) (-π) hopen.measurableSet]
  have hsub : Ioo (-ρ) ρ ⊆ Ioc (-π) (-π + 2 * π) := by
    intro θ hθ; constructor <;> linarith [hθ.1, hθ.2]
  have : ((↑) : ℝ → AddCircle (2 * π)) ⁻¹' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) ∩
      Ioc (-π) (-π + 2 * π) = Ioo (-ρ) ρ := by
    ext θ
    constructor
    · rintro ⟨⟨θ', h1, he⟩, h3⟩
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub h1) h3] at he
      exact he ▸ h1
    · intro h
      exact ⟨⟨θ, h, rfl⟩, hsub h⟩
  rw [this, Real.volume_Ioo]
  congr 1; ring

lemma finrank_lie : Module.finrank ℝ (lieE (UWb 0 r)) = 1 := by
  rw [lieE_eq]; exact finrank_span_singleton v0_ne

lemma vol_ball {ρ : ℝ} (h0 : 0 ≤ ρ) :
    volume (Metric.ball (0 : lieE (UWb 0 r)) ρ) = ENNReal.ofReal (2 * ρ) := by
  have : Nontrivial (lieE (UWb 0 r)) := Module.nontrivial_of_finrank_eq_succ finrank_lie
  rw [InnerProductSpace.volume_ball, finrank_lie]
  simp only [pow_one, Nat.cast_one]
  have hg : Real.Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have hs : √π / (√π / 2) = 2 := by
    have : √π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
    field_simp
  rw [hg, hs, ← ENNReal.ofReal_mul h0, mul_comm]

theorem gauge (r : ℕ) : IsGaugeOn (UWb 0 r) (μG r) := by
  refine ⟨isHaar, ?_⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ρ hρ
  rw [μG, me_Gm.map_apply, expBall_eq, Gm_injective.preimage_image, vol_arc hρ.2.le,
    vol_ball hρ.1.le, div_self]
  rw [ENNReal.toReal_ofReal (by linarith [hρ.1])]
  linarith [hρ.1]

end PI.ExistsGaugeMeasureForEachRank.W
