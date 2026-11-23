import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem latvol : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} = (modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} := by
  intro F _ _ _ _ _ _ ψ _ A
  set S : Set (Fin 2 → F) := {x | ∀ i, x i ∈ 𝒪[F]} with hS
  have hSo : IsOpen S := by
    have : S = Set.univ.pi fun _ => (𝒪[F] : Set F) := by
      ext x; simp [hS]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer
  have hSm : MeasurableSet S := hSo.measurableSet
  have hcont : Continuous fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hPm : MeasurableSet ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S) :=
    (hSo.preimage hcont).measurableSet
  have key := GlobalTheory.CompanionTheory.LFGTorus.integral_mulVec ψ A (S.indicator fun _ => (1 : ℂ))
  have e1 : (fun x : Fin 2 → F => S.indicator (fun _ => (1 : ℂ)) ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) =
      ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
    ext x
    by_cases h : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.1 h'))]
  rw [e1, integral_indicator_const _ hPm, integral_indicator_const _ hSm] at key
  have hmp : Ad3.mp (GeneralLinearGroup.det A) (-1) =
      (((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp [Ad3.mp, Complex.cpow_neg]
  rw [hmp] at key
  have : ((Ad3.LFS.vol2 ψ).real ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S) : ℂ) =
      (((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real S : ℝ) : ℂ) := by
    simpa using key
  exact_mod_cast this

end GlobalTheory.CompanionTheory.LFUDom
