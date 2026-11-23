import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBoxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.MixSumBound

variable {D : D7}

theorem finite_points_in_nhds (D : D7) (m n : ℕ) (K₀ : Set (Mx D m n)) (hK₀ : K₀ ∈ nhds (0 : Mx D m n)) :
    ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K₀ := by
  let K₁ : Set (Fin m → Fin n → AE D) := K₀
  have h1 : K₁ ∈ Filter.pi (fun _ : Fin m => nhds (0 : Fin n → AE D)) := by
    have : K₁ ∈ nhds (0 : Fin m → Fin n → AE D) := hK₀
    rwa [nhds_pi] at this
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 h1
  have h2 : ∀ i, ∃ J : Finset (Fin n), ∃ s : Fin n → Set (AE D), (∀ j, s j ∈ nhds (0 : AE D)) ∧
      (J : Set (Fin n)).pi s ⊆ t i := by
    intro i
    have h5 : t i ∈ Filter.pi (fun _ : Fin n => nhds (0 : AE D)) := by
      have : t i ∈ nhds (0 : Fin n → AE D) := ht i
      rwa [nhds_pi] at this
    exact Filter.mem_pi'.1 h5
  choose J s hs hJs using h2
  set V : Set (AE D) := ⋂ i, ⋂ j, s i j with hVdef
  have hV : V ∈ nhds (0 : AE D) := Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.exists_openAddSubgroup_finite_points_alt D V hV
  let U' : AddSubgroup (Mx D m n) :=
    { carrier := {u | ∀ i j, u i j ∈ U}
      add_mem' := fun ha hb i j => U.add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => U.zero_mem
      neg_mem' := fun ha i j => U.neg_mem (ha i j) }
  refine ⟨U', ?_, fun u hu hfin => ?_⟩
  · have : (U' : Set (Mx D m n)) = ⋂ i, ⋂ j, (fun u : Mx D m n => u i j) ⁻¹' (U : Set (AE D)) := by
      ext u; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact Iff.rfl
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hUo.preimage ((continuous_apply j).comp (continuous_apply i))
  · show u ∈ K₁
    apply hIt
    intro i _
    apply hJs i
    intro j _
    have h3 : infPart D (u i j) = 0 := by
      have := congrFun (congrFun hfin i) j
      simpa using this
    have h4 := hU _ (hu i j) h3
    simp only [hVdef, Set.mem_iInter] at h4
    exact h4 i j

theorem realSize_nsmul (θ : InfFam D) {m n : ℕ} (N : ℕ) (x : Mx D m n) :
    realSize θ (N • x) = N * realSize θ x := by
  unfold realSize compAt
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, norm_mul, Complex.norm_natCast]

theorem inv_pow_le (k N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    ((1 + r) ^ k)⁻¹ ≤ (N : ℝ) ^ k * ((1 + N * r) ^ k)⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < (1 + r) ^ k := by positivity
  have h2 : 0 < (1 + N * r) ^ k := by positivity
  rw [← div_eq_mul_inv, inv_le_comm₀ h1 (by positivity), inv_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) k

end GlobalTheory.MixSumBound

namespace GlobalTheory.MixSumBound

theorem mixS_tsum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), ∃ k : ℕ, ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ w, (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ) ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v
  obtain ⟨k, hk⟩ := GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top D θ hθ T.rank ρ
  refine ⟨k, fun K₀ hK₀ => ?_⟩
  obtain ⟨U, hUo, hU⟩ := finite_points_in_nhds D T.rank S.rank K₀ hK₀
  obtain ⟨K, hKc, hK⟩ := GlobalTheory.T.finiteAnnihilator_open_subgroup_in_box D ψ hψ S S₀ T ρ d U hUo
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v k
  have hM := hk K hKc
  refine ⟨C₁ * (∑' y : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k y)).toNNReal, fun n hn f hf hfix w => ?_⟩
  have hpt : ∀ x : Mx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤
      ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) * ENNReal.ofReal (maj θ K k (n • x)) := by
    intro x
    by_cases h0 : d.mixS T ψ v.μ v.𝓕 f x w = 0
    · simp [h0]
    have hbox : InBox K (n • x) := by
      apply hK
      intro a ha haU
      have hfin : (d.extY T a).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
      have hfix' := hfix _ (hU _ haU hfin) hfin
      have h2 := congrFun ((GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.1 x (n • a)) w
      rw [map_nsmul, hfix', Pi.smul_apply, smul_eq_mul] at h2
      have h3 : ψ (symplO S T (d.extX T x) (n • d.extY T a)) = 1 :=
        mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm)
      rw [map_nsmul, GlobalTheory.Mem.CoefInv.symplO_nsmul]
      exact h3
    have hmaj : maj θ K k (n • x) = ((1 + realSize θ (n • x)) ^ k)⁻¹ := by simp [maj, hbox]
    have hr := realSize_nonneg θ x
    have hdec := hC₁ f hf x w
    have hA : 0 < (1 + realSize θ x) ^ k := by positivity
    have hkey := inv_pow_le k n hn hr
    rw [← realSize_nsmul] at hkey
    calc ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ
        = ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ k) *
            ENNReal.ofReal (((1 + realSize θ x) ^ k)⁻¹) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul hA.le, mul_inv_cancel₀ hA.ne', ENNReal.ofReal_one, mul_one]
      _ ≤ (C₁ : ℝ≥0∞) * supSob ψ θ k f * ENNReal.ofReal ((n : ℝ) ^ k * ((1 + realSize θ (n • x)) ^ k)⁻¹) :=
          mul_le_mul' hdec (ENNReal.ofReal_le_ofReal hkey)
      _ = _ := by
          rw [hmaj, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          ring
  have hinj : Function.Injective fun x : ratMx D T.rank ρ => n • x := by
    intro x y hxy
    exact Subtype.ext (GlobalTheory.Mem.CoefInv.nsmul_cancel hn (congrArg Subtype.val hxy))
  calc (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ)
      ≤ ∑' x : ratMx D T.rank ρ, ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ENNReal.ofReal (maj θ K k ((n • x : ratMx D T.rank ρ) : Mx D T.rank ρ)) :=
        ENNReal.tsum_le_tsum fun x => by rw [AddSubgroup.coe_nsmul]; exact hpt x
    _ = ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ∑' x : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k ((n • x : ratMx D T.rank ρ) : Mx D T.rank ρ)) :=
        ENNReal.tsum_mul_left
    _ ≤ ((C₁ : ℝ≥0∞) * supSob ψ θ k f * (n : ℝ≥0∞) ^ k) *
          ∑' y : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K k y) :=
        mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj
          (fun y : ratMx D T.rank ρ => ENNReal.ofReal (maj θ K k y)))
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM]
        ring

end GlobalTheory.MixSumBound
