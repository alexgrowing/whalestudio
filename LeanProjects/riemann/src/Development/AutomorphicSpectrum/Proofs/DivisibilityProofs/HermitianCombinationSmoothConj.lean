import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem combLine_smooth_conj :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun hs => ?_, fun hc => ?_, ?_⟩
  · refine contDiffOn_prod fun j _ => ?_
    intro z hz
    have h0 : (ℓ j).h z ≠ 0 := ((ℓ j).pos z hz).ne'
    have hf := hs j z hz
    have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ j).h z ^ m)
        {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
      intro m
      cases m with
      | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
      | negSucc k =>
        simp only [zpow_negSucc]
        exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
    exact key _
  · intro z
    show (∏ j, (ℓ j).h _ ^ n j) = ∏ j, (ℓ j).h z ^ n j
    simp only [hc _ z]
  · exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.Top
