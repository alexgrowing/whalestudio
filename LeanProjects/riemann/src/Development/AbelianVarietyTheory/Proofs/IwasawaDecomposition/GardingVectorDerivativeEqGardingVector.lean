import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVec

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def fieldDeriv (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ) where
  toFun X g := fderiv ℝ φ g (-(P * X * P⁻¹) * g)
  map_add' X Y := by
    funext g
    simp only [Pi.add_apply, ← map_add, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, ← map_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]

theorem isTest_fderiv {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest fun g => fderiv ℝ φ g (Y * g) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (le_of_eq rfl)).clm_apply (contDiff_const.mul contDiff_id), ?_⟩
  refine HasCompactSupport.intro hφ.2 fun g hg => ?_
  rw [fderiv_of_notMem_tsupport ℝ hg]; rfl

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem hasDerivAt_integral_translate (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}
    (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    HasDerivAt (fun t : ℝ => ∫ g : Formalism.REAL.UJ ε, φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
      ∂(Formalism.REAL.muG ε)) (gard ε σ (fun g => fderiv ℝ φ g (Y * g)) w) 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := continuous_umat
  have hb := continuous_orbit hσ w
  have he : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (Z * NormedSpace.exp (t • Z)) t :=
    fun Z t => hasDerivAt_exp_smul_const' Z t
  have hc : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
    fun Z => continuous_iff_continuousAt.2 fun t => (he Z t).continuousAt
  have hxy : ∀ t : ℝ, NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_left.smul_left t).smul_right t), ← smul_add]
    simp
  have hC : IsCompact (Set.image2 (· * ·) ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1)
      (tsupport φ)) := ((isCompact_closedBall (0 : ℝ) 1).image (hc _)).mul hφ.2
  have hK := hemb.isCompact_preimage hC
  set K := (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹' (Set.image2 (· * ·)
    ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1) (tsupport φ)) with hKdef
  replace hK : IsCompact K := hK
  have hout : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g ∉ K, NormedSpace.exp (t • Y) * umat g ∉ tsupport φ :=
    fun t ht g hg hm => hg ⟨_, ⟨t, ht, rfl⟩, _, hm, by
      show _ * (_ * _) = umat g
      rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]⟩
  set μ := Formalism.REAL.muG ε
  let F' : ℝ → Formalism.REAL.UJ ε → H := fun t g =>
    fderiv ℝ φ (NormedSpace.exp (t • Y) * umat g) (Y * NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
  have hF'c : Continuous fun p : ℝ × Formalism.REAL.UJ ε => F' p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => NormedSpace.exp (p.1 • Y) := (hc Y).comp continuous_fst
    have h2 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => umat p.2 := hu.comp continuous_snd
    exact (((hφ.1.continuous_fderiv (by simp)).comp (h1.mul h2)).clm_apply
      ((continuous_const.mul h1).mul h2)).smul (hb.comp continuous_snd)
  obtain ⟨C, hCb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  have hint : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, Integrable
      (fun g : Formalism.REAL.UJ ε => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) μ := fun t ht =>
    Continuous.integrable_of_hasCompactSupport ((hφ.continuous.comp (continuous_const.mul hu)).smul hb)
      (HasCompactSupport.intro hK fun g hg => by
        rw [image_eq_zero_of_notMem_tsupport (hout t ht g hg), zero_smul])
  have e0 : F' 0 = fun g : Formalism.REAL.UJ ε => fderiv ℝ φ (umat g) (Y * umat g) • σ (umat g) w := by
    funext g; simp [F']
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t g => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) (F' := F')
    (bound := K.indicator fun _ => C) (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    (by filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
        exact (hint t ht).aestronglyMeasurable)
    (hint 0 (Metric.mem_closedBall_self zero_le_one))
    (by rw [e0]; exact ((isTest_fderiv hφ Y).integrable hb).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g t ht => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg]; exact hCb (t, g) ⟨ht, hg⟩
      · rw [Set.indicator_of_notMem hg]
        simp [F', fderiv_of_notMem_tsupport ℝ (hout t ht g hg)])
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun g t _ =>
      (((hφ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ((he Y t).mul_const (umat g))).smul_const _)
  rw [e0] at key
  exact key.2

theorem dRep_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  intro n ε H _ _ _ σ P G hP h hσ φ hφ
  refine ⟨fieldDeriv φ P, fun X => ⟨isTest_fderiv hφ _, fun hX w => ?_⟩⟩
  refine Eq.trans ?_ (hasDerivAt_integral_translate hσ hφ (-(P * X * P⁻¹)) w).deriv
  unfold dRep
  congr 1
  funext t
  rw [gard_eq hσ hφ]
  refine GlobalTheory.LowTypeRestriction.garding_translate hσ hφ.continuous hφ.2 w
    (conj_mem_UJ hP h (exp_mem_UH (gram_unit hP h) hX t)) ?_
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl (P * X * P⁻¹)).neg_left.smul_left t).smul_right t), ← smul_add]
  simp

end GlobalTheory.SmVec

end
