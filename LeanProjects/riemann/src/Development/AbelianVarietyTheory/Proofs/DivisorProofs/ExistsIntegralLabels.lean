import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTorsionEqPeriodLatticeModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDegenerationTorsionClassicalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_integral_labels : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q → ∃ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, (∀ a, d.Rep σ k (M a) (Nn a) (q a)) ∧ (∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ) := by
  intro N g' r g bX d σ k hk ζ q hq
  obtain ⟨-, hadd, hinj, hsurj, hwp⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.degenerationTorsion_eq_periodLattice_mod_level N g' r g bX d σ k hk
  have h5 := GlobalTheory.T.weilPairing_degenerationTorsion_classical N g' r g bX d σ k hk
  choose M0 N0 hMN using h1
  refine ⟨fun a => M0 (q a), fun a => N0 (q a), fun a => hMN _, fun a a' => ?_, fun a a' M' N' hM hN => ?_,
    fun M₁ N₁ => ?_, fun i j => ?_⟩
  · exact (h4 _ _ _ _ _ _ (h3 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))) (hMN (q (a + a')))).1 (hadd a a')
  · exact hinj a a' ((h4 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))).2 ⟨M', N', hM, hN⟩)
  · obtain ⟨p, hp, -⟩ := h2 M₁ N₁
    obtain ⟨a, ha⟩ := hsurj p
    exact ⟨a, (h4 _ _ _ _ _ _ (hMN (q a)) hp).1 ha⟩
  · rw [← hwp i j]
    exact (h5 _ _ _ _ _ _ (hMN _) (hMN _)).symm

end GlobalTheory.MBLow.Cl
