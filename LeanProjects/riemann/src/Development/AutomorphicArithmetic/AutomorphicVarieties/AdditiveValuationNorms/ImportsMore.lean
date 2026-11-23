import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsTer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.step :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (w : Module.End ℤ_[l] X), GenBy l R X → InPow 2 (w - 1) →
      cokLen (w ^ l - 1) ≤ cokLen (w - 1) + R := by
  intro l _ X _ _ R w hG hw
  haveI : Module.Finite ℤ_[l] X := by
    obtain ⟨π, hπ⟩ := hG
    exact Module.Finite.of_surjective π hπ
  have h1 := (UpperTheory.V.Base.lenComp ℤ_[l] X (∑ i ∈ Finset.range l, w ^ i) (w - 1)).2
  rw [geom_sum_mul] at h1
  have h2 := cokLen_le_of_range_le (phi l X w hw)
  have h3 := cokL l X R hG
  calc cokLen (w ^ l - 1) ≤ cokLen (∑ i ∈ Finset.range l, w ^ i) + cokLen (w - 1) := h1
    _ ≤ R + cokLen (w - 1) := add_le_add_left (h2.trans h3) _
    _ = cokLen (w - 1) + R := add_comm _ _
