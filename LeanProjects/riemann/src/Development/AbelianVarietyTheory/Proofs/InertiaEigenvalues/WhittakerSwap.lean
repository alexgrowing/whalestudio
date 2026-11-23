import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (u v : A.K) :
    A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
  unfold psiK
  rw [map_add, AddChar.map_add_eq_mul]

theorem psiK_continuous (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) := by
  have h1 : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact (DualLattice.stdChar_continuous hψ).comp h1

theorem NL_continuous [Unram F E] (A : Et F E) : Continuous A.NL := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [this]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hlin : Continuous (((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F) :=
    IsModuleTopology.continuous_of_linearMap _
  convert hlin using 1
  funext y
  simp [Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.Et

namespace GlobalTheory.JR.Et

theorem whittaker_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  intro F E _ _ _ _ _ A ψ hψ μK _ μ _ φ hφ x a c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  set M : Set A.K := {z : A.K | c • z ∈ A.OK} with hMdef
  have hOKclosed : IsClosed A.OK := by
    have : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by
      change IsOpen (R : Set A.K); rw [hR]; exact hOpen
    have h2 := AddSubgroup.isClosed_of_isOpen _ this
    change IsClosed (R : Set A.K) at h2
    rwa [hR] at h2
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMopen : IsOpen M := hOpen.preimage hsm
  have hMclosed : IsClosed M := hOKclosed.preimage hsm
  have hMcpt : IsCompact M := by
    have : M = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        change c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]
    exact hCpt.image (continuous_const_smul _)
  have hMmeas : MeasurableSet M := hMopen.measurableSet
  let g : A.K → A.L → ℂ := fun z y => φ y * A.psiK ψ (z * (x * A.NL y - a))
  let f : A.K → A.L → ℂ := fun z y => M.indicator (fun _ => (1 : ℂ)) z * g z y
  have hpt : ∀ z y, φ y * A.psiK ψ (z * x * A.NL y) * A.psiK ψ (-(a * z)) = g z y := by
    intro z y
    simp only [g]
    rw [mul_assoc, ← psiK_add]
    congr 2
    ring
  have hL : ∀ z, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) = ∫ y, g z y ∂μ := by
    intro z
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => hpt z y)
  have hind : ∀ (h : A.K → ℂ) z, M.indicator (fun _ => (1 : ℂ)) z * h z = M.indicator h z := by
    intro h z
    by_cases hz : z ∈ M <;> simp [hz]
  have hcontI : Continuous (M.indicator (fun _ : A.K => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hMclosed, hMopen⟩ continuous_const
  have hφc : Continuous φ := hφ.1.continuous
  have hcont : Continuous (Function.uncurry f) := by
    have hN := A.NL_continuous
    have hP := A.psiK_continuous hψ
    refine (hcontI.comp continuous_fst).mul ((hφc.comp continuous_snd).mul (hP.comp ?_))
    exact continuous_fst.mul (((continuous_const.mul (hN.comp continuous_snd))).sub continuous_const)
  have hsupp : HasCompactSupport (Function.uncurry f) := by
    have hsub : Function.support (Function.uncurry f) ⊆ M ×ˢ tsupport φ := by
      rintro ⟨z, y⟩ hzy
      simp only [Function.mem_support, Function.uncurry_apply_pair, f, g] at hzy
      refine ⟨?_, subset_tsupport _ ?_⟩
      · by_contra hz
        exact hzy (by simp [hz])
      · intro h0
        exact hzy (by simp [h0])
    exact IsCompact.of_isClosed_subset (hMcpt.prod hφ.2) (isClosed_tsupport _)
      (closure_minimal hsub (hMclosed.prod (isClosed_tsupport _)))
  have hswap := integral_integral_swap_of_hasCompactSupport hcont hsupp (μ := μK) (ν := μ)
  calc ∫ z in M, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK
      = ∫ z in M, (∫ y, g z y ∂μ) ∂μK := setIntegral_congr_fun hMmeas (fun z _ => hL z)
    _ = ∫ z, M.indicator (fun z => ∫ y, g z y ∂μ) z ∂μK := (integral_indicator hMmeas).symm
    _ = ∫ z, ∫ y, f z y ∂μ ∂μK := by
      congr 1 with z
      rw [← hind, ← integral_const_mul]
    _ = ∫ y, ∫ z, f z y ∂μK ∂μ := hswap
    _ = ∫ y, φ y * ∫ z in M, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
      congr 1 with y
      rw [← integral_const_mul, ← integral_indicator hMmeas]
      congr 1 with z
      rw [← hind]

end GlobalTheory.JR.Et
