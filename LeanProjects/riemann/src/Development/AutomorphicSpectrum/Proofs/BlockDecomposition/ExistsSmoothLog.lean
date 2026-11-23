import Formalism.UnipotentAdelicQuotients.SmComplete
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SmoothLog

theorem exists_log_banach (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    ∃ (U : Set A) (L : A → A), IsOpen U ∧ (1 : A) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧
      (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧
      (∀ᶠ X in 𝓝 (0 : A), L (NormedSpace.exp X) = X) := by
  let e := CompanionTheory.D.Upq.expPartialHomeomorph ℝ A
  refine ⟨e.target, e.symm, e.open_target, CompanionTheory.D.Upq.one_mem_expPartialHomeomorph_target ℝ A,
    CompanionTheory.D.Upq.contDiffOn_expPartialHomeomorph_symm ℝ A,
    CompanionTheory.D.Upq.expPartialHomeomorph_symm_one ℝ A, fun g hg => e.right_inv hg, ?_⟩
  filter_upwards [e.open_source.mem_nhds (CompanionTheory.D.Upq.zero_mem_expPartialHomeomorph_source ℝ A)]
    with X hX using e.left_inv hX

def OpMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

instance (n : ℕ) : NormedRing (OpMat n) := Matrix.linftyOpNormedRing
instance (n : ℕ) : NormedAlgebra ℝ (OpMat n) := Matrix.linftyOpNormedAlgebra
instance (n : ℕ) : FiniteDimensional ℝ (OpMat n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
instance (n : ℕ) : CompleteSpace (OpMat n) := FiniteDimensional.complete ℝ _

def toOp (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] OpMat n :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ))

theorem exists_smooth_log : ∀ (n : ℕ), ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧ (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧ (∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X) ∧ ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by
  intro n
  obtain ⟨U, L, hU, h1, hL, hL1, hexp, hev⟩ := exists_log_banach (OpMat n)
  let φ := toOp n
  have hφexp : ∀ X, NormedSpace.exp (φ X) = φ (NormedSpace.exp X) := fun _ => rfl
  refine ⟨φ ⁻¹' U, fun g => φ.symm (L (φ g)), hU.preimage φ.continuous, h1, ?_, ?_, ?_, ?_, ?_⟩
  · exact φ.symm.contDiff.comp_contDiffOn (hL.comp φ.contDiff.contDiffOn fun _ hx => hx)
  · change φ.symm (L 1) = 0
    rw [hL1, map_zero]
  · intro g hg
    apply φ.injective
    rw [← hφexp, φ.apply_symm_apply]
    exact hexp _ hg
  · have ht : Tendsto φ (𝓝 0) (𝓝 0) := by
      simpa using φ.continuous.tendsto 0
    filter_upwards [ht.eventually hev] with X hX
    change φ.symm (L (φ (NormedSpace.exp X))) = X
    rw [← hφexp, hX, φ.symm_apply_apply]
  · exact φ.symm.contDiff.comp ((CompanionTheory.D.Upq.contDiff_exp ℝ (OpMat n)).comp φ.contDiff)

end GlobalTheory.CompanionTheory.SmoothLog
