import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem whittaker_torus_value_formula (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (ν : Fˣ →* ℂˣ) (a b : ℤ) :
    (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
      sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
    (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  have hψ₀ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
    intro x hx
    obtain ⟨hc, h1, h0⟩ := hψ
    have ht := isTrivialOn_addCharConductor hc h1
    rw [h0] at ht
    have := ht x (mem_valBall_zero_iff.2 hx)
    show ((ψ x : Circle) : ℂ) = 1
    rw [this, Circle.coe_one]
  have hanti : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : rhoPair (![a, b] : Fin 2 → ℤ) = a - b := by
    simp [rhoPair, Fin.sum_univ_two]
    ring
  have key := sphericalWhittaker_torusPow hψ₀ ![ν (unifUnit F), ν⁻¹ (unifUnit F)] ![a, b]
  rw [MonoidHom.inv_apply] at key
  unfold Ad3.LFS.s2
  rw [MonoidHom.inv_apply, key]
  constructor
  · intro h
    rw [if_pos (hanti.2 h), halfModulus_eq, hrho]
  · intro h
    rw [if_neg (fun h' => absurd (hanti.1 h') (not_le.2 h))]

end GlobalTheory.CompanionTheory.LFUDom
