import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedDiagonalAction
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2

theorem diag_uniformizer_eq_torus_mul_integral {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a b : ℤ) :
    ∃ k ∈ GLnLocal.integralGL F 2, (d2 (unifUnit F ^ a) (unifUnit F ^ b) : GL (Fin 2) F) =
      Iwasawa.torusPow F 2 ![a, b] * k := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F (unifUnit F ^ a)
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F (unifUnit F ^ b)
  rw [ord_unifUnit_zpow] at hu hv
  refine ⟨GLnLocal.integralGLHom F 2 (d2 u v), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, Iwasawa.coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [d2, GLnLocal.integralGLHom, Matrix.diagonal_mul, ← hu, ← hv]

theorem spherical_whittaker_GL2_uniformizer_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![a, b]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ y a b
  obtain ⟨k, hk, hdg⟩ := diag_uniformizer_eq_torus_mul_integral (F := F) a b
  have hanti : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : Spherical.rhoPair (![a, b] : Fin 2 → ℤ) = a - b := by
    simp [Spherical.rhoPair, Fin.sum_univ_two]
    ring
  rw [hdg, Spherical.sphericalWhittaker_mul_right hψ₀ _ _ hk,
    Spherical.sphericalWhittaker_torusPow hψ₀]
  by_cases h : b ≤ a
  · rw [if_pos (hanti.2 h), if_pos h, Spherical.halfModulus_eq, hrho]
  · rw [if_neg (fun h' => h (hanti.1 h')), if_neg h]

end GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2
