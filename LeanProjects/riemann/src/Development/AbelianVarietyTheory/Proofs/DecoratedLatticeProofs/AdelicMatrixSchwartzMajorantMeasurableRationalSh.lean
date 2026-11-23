import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf.MajMeas

variable {D : D7}

theorem norm_compAt_le_realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m)
    (j : Fin n) : ‖compAt θ τ x i j‖ ≤ realSize θ x := by
  unfold realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ', ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖ :=
        Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} :
    Continuous (realSize θ : Mx D m n → ℝ) := by
  unfold realSize
  refine continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_norm.comp ((GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j))

theorem finPart_eq_zero_iff {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (a : AE D) : finPart D a = 0 ↔ a = σ (fun τ => θ τ (infPart D a)) := by
  constructor
  · intro ha
    refine sub_eq_zero.1 (h.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, h.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, h.comp, sub_self]
  · intro ha
    rw [ha]
    exact h.fin _

theorem isClosed_finZero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (m n : ℕ) : IsClosed {z : Mx D m n | z.map (finPart D) = 0} := by
  obtain ⟨-, h2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have e : {z : Mx D m n | z.map (finPart D) = 0} =
      ⋂ i, ⋂ j, {z : Mx D m n | z i j = σ (fun τ => θ τ (infPart D (z i j)))} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hz i j
      have hz' := congrFun (congrFun hz i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at hz'
      exact (finPart_eq_zero_iff h _).1 hz'
    · intro hz
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact (finPart_eq_zero_iff h _).2 (hz i j)
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_id.matrix_elem i j) ?_
  exact h.cont.comp (continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_id.matrix_elem i j))

theorem setOf_inBox {m n : ℕ} (K : Set (Mx D m n)) :
    {x | InBox K x} = K + {z : Mx D m n | z.map (finPart D) = 0} := by
  ext x
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, x - k, hx, add_sub_cancel k x⟩
  · rintro ⟨k, hk, z, hz, rfl⟩
    exact ⟨k, hk, by rwa [add_sub_cancel_left]⟩

theorem isClosed_inBox {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) : IsClosed {x | InBox K x} := by
  obtain ⟨h1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  rw [setOf_inBox]
  exact (isClosed_finZero h m n).add_left_of_isCompact hK

theorem isCompact_box {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (R : ℝ) :
    IsCompact {x | InBox K x ∧ realSize θ x ≤ R} := by
  obtain ⟨h1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  let B : Set (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let g : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) → Mx D m n := fun p =>
    p.1 + Matrix.of fun i j => σ (fun τ => p.2 τ i j - θ τ (infPart D (p.1 i j)))
  have hg : Continuous g := by
    refine continuous_fst.add (continuous_matrix fun i j => h.cont.comp (continuous_pi fun τ => ?_))
    have c1 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => p.2 τ i j := by fun_prop
    have c2 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => θ τ (infPart D (p.1 i j)) :=
      (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_fst.matrix_elem i j)
    exact c1.sub c2
  refine ((hK.prod hB).image hg).of_isClosed_subset
    ((isClosed_inBox h K hK).inter (isClosed_le (continuous_realSize h.inf) continuous_const)) ?_
  rintro x ⟨⟨k, hk, hx⟩, hR⟩
  refine ⟨(k, fun τ i j => θ τ (infPart D (x i j))), ⟨hk, fun τ _ i _ j _ => ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_compAt_le_realSize θ x τ i j).trans hR
  · ext i j
    have h0 := congrFun (congrFun hx i) j
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply] at h0
    have e := (finPart_eq_zero_iff h _).1 h0
    simp only [(infPart D).map_sub, (θ _).map_sub] at e
    show k i j + σ (fun τ => θ τ (infPart D (x i j)) - θ τ (infPart D (k i j))) = x i j
    rw [← e, add_sub_cancel]

theorem measurable_maj {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (N : ℕ) : Measurable (maj θ K N) := by
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  unfold maj
  exact Measurable.ite (isClosed_inBox h K hK).measurableSet
    ((continuous_const.add (continuous_realSize h.inf)).pow N).measurable.inv measurable_const

theorem exists_leftInv {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) : ∃ y : Matrix (Fin n) (Fin m) D.host.E, y * x = 1 := by
  have hinj : Function.Injective x.mulVecLin := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective x.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  rwa [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {m n k : ℕ} (A : Mx D m n) (B : Mx D n k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem realSize_mul_le (θ : InfFam D) {m n k : ℕ} (Y : Mx D m n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : Mx D n k, realSize θ (Y * a) ≤ c * realSize θ a := by
  refine ⟨∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖, by positivity, fun a => ?_⟩
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

theorem maj_rat_le (θ : InfFam D) (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) (K : Set (Mx D m k)) (hK : IsCompact K) :
    ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k,
      maj θ K N ((rat x : Mx D m n) * u) ≤ C * maj θ K' N u := by
  obtain ⟨h1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  obtain ⟨y, hy⟩ := exists_leftInv x hx
  have hyx : (rat y : Mx D n m) * rat x = 1 := by
    unfold rat
    rw [← Matrix.map_mul, hy, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c, hc0, hc⟩ := realSize_mul_le θ (k := k) (rat y : Mx D n m)
  refine ⟨(fun a => (rat y : Mx D n m) * a) '' K, hK.image (continuous_const.matrix_mul continuous_id),
    fun N => ⟨(1 + c) ^ N, fun u => ?_⟩⟩
  by_cases hb : InBox K ((rat x : Mx D m n) * u)
  · obtain ⟨k0, hk0, hkx⟩ := hb
    have hb' : InBox ((fun a => (rat y : Mx D n m) * a) '' K) u := by
      refine ⟨rat y * k0, ⟨k0, hk0, rfl⟩, ?_⟩
      have e : u - rat y * k0 = rat y * (rat x * u - k0) := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
      rw [e, Matrix.map_mul, hkx, Matrix.mul_zero]
    simp only [maj, if_pos (show InBox K ((rat x : Mx D m n) * u) from ⟨k0, hk0, hkx⟩), if_pos hb']
    have hs := hc ((rat x : Mx D m n) * u)
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul] at hs
    have h0 := realSize_nonneg θ ((rat x : Mx D m n) * u)
    have h0' := realSize_nonneg θ u
    have hle : 1 + realSize θ u ≤ (1 + c) * (1 + realSize θ ((rat x : Mx D m n) * u)) := by nlinarith
    have hA : 0 < (1 + realSize θ ((rat x : Mx D m n) * u)) ^ N := by positivity
    have hB : 0 < (1 + realSize θ u) ^ N := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  · have e : maj θ K N ((rat x : Mx D m n) * u) = 0 := by simp only [maj, if_neg hb]
    rw [e]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N u)

end GlobalTheory.Unf.MajMeas

open GlobalTheory.Unf.MajMeas in

theorem GlobalTheory.Unf.maj_measurable_rat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  intro D θ hθ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact ⟨fun m n K hK => ⟨isClosed_inBox hσ K hK, continuous_realSize hθ, fun N => measurable_maj hσ K hK N,
    fun R => isCompact_box hσ K hK R⟩, fun m n k x hx K hK => maj_rat_le θ m n k x hx K hK⟩

end
