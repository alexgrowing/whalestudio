import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Assembly
import GroundTheory.HeightsAndTheta.Heights.Slopes.PRelSlopeQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas

noncomputable section

section Had

variable {K : Type} [Field K] [NumberField K]

theorem bundleDegree_eq_deg (E : HermitianBundle.{0} K) : bundleDegree E = E.deg := by
  rw [bundleDegree, HermitianBundle.normDegree_eq_deg_sub, ChainSum.deg_sub_top]

def saturation {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] (F : Submodule (𝓞 K) M) :
    Submodule (𝓞 K) M where
  carrier := {x | ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ F}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    have : (b * a) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
    rw [this]
    exact F.add_mem (F.smul_mem b hx) (F.smul_mem a hy)
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact F.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact F.smul_mem c hx

theorem le_saturation {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] (F : Submodule (𝓞 K) M) :
    F ≤ saturation F :=
  fun x hx ↦ ⟨1, one_ne_zero, by rwa [one_smul]⟩

theorem saturated_saturation (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) :
    E.Saturated (saturation F) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

theorem finrank_saturation (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) :
    Module.finrank (𝓞 K) (saturation F) = Module.finrank (𝓞 K) F := by
  set P := saturation F
  set F' := F.comap P.subtype
  have h0 : Module.finrank (𝓞 K) (P ⧸ F') = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro x
    obtain ⟨⟨x, a, ha, hx⟩, rfl⟩ := F'.mkQ_surjective x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have h1 := F'.finrank_quotient_add_finrank
  rw [h0, zero_add] at h1
  rw [← h1]
  exact (Submodule.comapSubtypeEquivOfLe (le_saturation F)).finrank_eq

theorem norm_comap (E' E : HermitianBundle.{0} K) (f : E'.carrier →ₗ[𝓞 K] E.carrier)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x : Fibre σ E'.carrier) :
    ‖FibreSpace.equiv (E.metric.comap f hf) σ x‖ = fibreNorm E σ (f.lTensor (ComplexAt σ) x) := by
  have h : ‖FibreSpace.equiv (E.metric.comap f hf) σ x‖ ^ 2 =
      fibreNorm E σ (f.lTensor (ComplexAt σ) x) ^ 2 := by
    rw [fibreNorm, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, FibreSpace.inner_equiv,
      FibreSpace.inner_equiv, HermitianMetric.comap_inner]
    rfl
  have h1 := norm_nonneg (FibreSpace.equiv (E.metric.comap f hf) σ x)
  have h2 : 0 ≤ fibreNorm E σ (f.lTensor (ComplexAt σ) x) := norm_nonneg _
  nlinarith [sq_nonneg (‖FibreSpace.equiv (E.metric.comap f hf) σ x‖ -
    fibreNorm E σ (f.lTensor (ComplexAt σ) x)), sq_nonneg (‖FibreSpace.equiv (E.metric.comap f hf) σ x‖ +
    fibreNorm E σ (f.lTensor (ComplexAt σ) x))]

theorem sum_log_le (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) (F : ShortFamily E lam)
    {k : ℕ} (s : Fin k → Fin (bundleRank E)) :
    ∑ j, ∑ σ : K →+* ℂ, Real.log (E.normAt σ (F.vec (s j))) ≤
      k * ∑ σ : K →+* ℂ, Real.log (lam σ) := by
  have h : ∀ j, ∑ σ : K →+* ℂ, Real.log (E.normAt σ (F.vec (s j))) ≤
      ∑ σ : K →+* ℂ, Real.log (lam σ) := fun j ↦ Finset.sum_le_sum fun σ _ ↦ by
    have hpos : 0 < E.normAt σ (F.vec (s j)) :=
      norm_pos_iff.mpr ((linearIndependent_fibreVec E.metric σ F.linearIndependent).ne_zero (s j))
    exact Real.log_le_log hpos (F.norm_le σ (s j))
  calc _ ≤ ∑ _j : Fin k, ∑ σ : K →+* ℂ, Real.log (lam σ) := Finset.sum_le_sum fun j _ ↦ h j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Had

theorem Had.proof : Had.Statement := by
  refine ⟨?_, ?_⟩
  · intro K _ _ E' E A lam α F
    set f := α.toLinearMap
    have hf := α.injective
    set R := LinearMap.range f
    set P := saturation R
    have hP := saturated_saturation E R
    have hRP := le_saturation R
    set n : ℝ := (Module.finrank ℚ K : ℝ) with hn_def
    have hn : 0 < n := Nat.cast_pos.mpr Module.finrank_pos

    have h1 := NormComparison.full.{0, 0} K E' (E.metric.comap f hf) A fun σ x ↦ by
      rw [norm_comap]; exact α.norm_le σ x

    have h2 : (⟨E'.carrier, E.metric.comap f hf⟩ : HermitianBundle.{0} K).deg = (E.sub R).deg :=
      ChainSum.deg_eq_of_linearEquiv _ _ (LinearEquiv.ofInjective f hf) fun σ m s ↦ by
        rw [gramDet_comap E.metric f hf σ s]
        exact (gramDet_comap E.metric R.subtype R.injective_subtype σ
          (fun i ↦ LinearEquiv.ofInjective f hf (s i))).symm

    have hrk : Module.finrank (𝓞 K) (R.comap P.subtype) =
        Module.finrank (𝓞 K) (E.sub P).carrier := by
      rw [(Submodule.comapSubtypeEquivOfLe hRP).finrank_eq]
      exact (finrank_saturation E R).symm
    have h3 := (Sublattice.full.{0, 0} K (E.sub P) (R.comap P.subtype) hrk).2
    rw [ChainSum.deg_sub_comap E hRP] at h3

    have h4 := ExactSequence.full.{0, 0} K E P hP

    have hspan : Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range F.vec)) =
        Module.finrank (𝓞 K) E.carrier := by
      rw [finrank_span_eq_card F.linearIndependent, Fintype.card_fin]
    obtain ⟨s, -, h5⟩ := HadamardMeanQuotient.full.{0, 0, 0} K E P hP F.vec hspan
    have h6 := sum_log_le E lam F s

    have hq : ((Module.finrank (𝓞 K) (E.carrier ⧸ P) : ℕ) : ℝ) =
        (bundleRank E : ℝ) - bundleRank E' := by
      have e1 := P.finrank_quotient_add_finrank
      have e2 : Module.finrank (𝓞 K) P = bundleRank E' := by
        rw [finrank_saturation E R]; exact LinearMap.finrank_range_of_inj hf
      rw [e2] at e1
      rw [eq_sub_iff_add_eq]
      exact_mod_cast e1
    rw [hq] at h6
    rw [bundleDegree_eq_deg, bundleDegree_eq_deg, meanLog, meanLog]
    have h7 : -(((bundleRank E : ℝ) - bundleRank E') * ∑ σ : K →+* ℂ, Real.log (lam σ)) / n ≤
        -(∑ j, ∑ σ : K →+* ℂ, Real.log (E.normAt σ (F.vec (s j)))) / n := by
      apply div_le_div_of_nonneg_right _ hn.le
      linarith
    have e3 : (bundleRank E' : ℝ) * ((∑ σ : K →+* ℂ, Real.log (A σ)) / n) =
        Module.finrank (𝓞 K) E'.carrier * (∑ σ : K →+* ℂ, Real.log (A σ)) / n := by ring
    have e4 : ((bundleRank E : ℝ) - bundleRank E') * ((∑ σ : K →+* ℂ, Real.log (lam σ)) / n) =
        -(-(((bundleRank E : ℝ) - bundleRank E') * ∑ σ : K →+* ℂ, Real.log (lam σ)) / n) := by ring
    rw [e3, e4]
    linarith
  · intro K _ _ E lam F
    set n : ℝ := (Module.finrank ℚ K : ℝ) with hn_def
    have hn : 0 < n := Nat.cast_pos.mpr Module.finrank_pos
    have h1 := HadamardMean.full.{0, 0, 0} K E F.vec F.linearIndependent (Fintype.card_fin _)
    have h2 := sum_log_le E lam F id
    rw [bundleDegree_eq_deg, meanLog]
    have h3 : -((bundleRank E : ℝ) * ∑ σ : K →+* ℂ, Real.log (lam σ)) / n ≤
        -(∑ j, ∑ σ : K →+* ℂ, Real.log (E.normAt σ (F.vec (id j)))) / n := by
      apply div_le_div_of_nonneg_right _ hn.le
      linarith
    have e : -((bundleRank E : ℝ) * ((∑ σ : K →+* ℂ, Real.log (lam σ)) / n)) =
        -((bundleRank E : ℝ) * ∑ σ : K →+* ℂ, Real.log (lam σ)) / n := by ring
    rw [e]
    exact h3.trans h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
