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

namespace GlobalTheory.CompanionTheory.SphGL3

theorem antitone_triple_iff (a b : ℤ) : Antitone (![a, b, 0] : Fin 3 → ℤ) ↔ b ≤ a ∧ 0 ≤ b := by
  constructor
  · intro h
    exact ⟨by simpa using h (show (0 : Fin 3) ≤ 1 by decide),
      by simpa using h (show (1 : Fin 3) ≤ 2 by decide)⟩
  · rintro ⟨h1, h2⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem rhoPair_triple (a b : ℤ) : GroundTheory.Automorphic.Spherical.rhoPair (![a, b, 0] : Fin 3 → ℤ) = 2 * a := by
  simp [GroundTheory.Automorphic.Spherical.rhoPair, Fin.sum_univ_three]

theorem sph_dg_zpow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![a, b, 0]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ z a b
  obtain ⟨k, hk, hdg⟩ := GlobalTheory.CompanionTheory.LocalUnramified.sDg F (unifUnit F ^ a) (unifUnit F ^ b) 1
  have o1 : ord (((unifUnit F ^ a : Fˣ)) : F) = a := ord_unifUnit_zpow a
  have o2 : ord (((unifUnit F ^ b : Fˣ)) : F) = b := ord_unifUnit_zpow b
  have o3 : ord (((1 : Fˣ)) : F) = 0 := by simp [ord]
  rw [o1, o2, o3] at hdg
  rw [hdg, Spherical.sphericalWhittaker_mul_right hψ₀ _ _ hk, Spherical.sphericalWhittaker_torusPow hψ₀]
  by_cases h : b ≤ a ∧ 0 ≤ b
  · have hsq2 : Spherical.sqrtQ F ^ 2 = (residueCard F : ℂ) := by
      rw [Spherical.sqrtQ_sq]
      rfl
    rw [if_pos ((antitone_triple_iff a b).2 h), if_pos h, Spherical.halfModulus_eq, rhoPair_triple,
      show -(2 * a) = (2 : ℤ) * (-a) by ring, _root_.zpow_mul, zpow_ofNat, hsq2]
  · rw [if_neg (fun h' => h ((antitone_triple_iff a b).1 h')), if_neg h]

end GlobalTheory.CompanionTheory.SphGL3
