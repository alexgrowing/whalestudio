import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitApprox

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {p : ℕ} [Fact p.Prime]

theorem int_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem int_sub {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a - c) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hc v)

theorem int_natCast (k : ℕ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_natCast]; exact natCast_mem _ k

theorem exists_int_approx : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  intro p _ ε ε' hε hε' hεε'
  classical
  let u : ℕ → ℤ := fun n => if h : 0 < n ∧ n.Coprime p then
    Classical.choose (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε) else 0
  have hu : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
    intro n hn hnp
    have h : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    have hs := Classical.choose_spec (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε)
    have e : u n = Classical.choose (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε) := by
      simp only [u, dif_pos h]
    rw [e]; exact hs
  refine ⟨u, ?_, ?_⟩
  · intro n m hn hm hnmp
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnmp
    obtain ⟨β, hβ, e1⟩ := hu n hn hnp
    obtain ⟨β', hβ', e2⟩ := hu (n * m) (Nat.mul_pos hn hm) hnmp
    apply IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ (β - (m : AfP p) * β')
      (int_sub hβ (int_mul (int_natCast m) hβ'))
    have : ((u (n * m) - u n : ℤ) : AfP p) = (u (n * m) : AfP p) - (u n : AfP p) := by push_cast; ring
    rw [this]
    have e3 : (u (n * m) : AfP p) = ε - ((n * m : ℕ) : AfP p) * β' := by rw [e2]; ring
    have e4 : (u n : AfP p) = ε - (n : AfP p) * β := by rw [e1]; ring
    rw [e3, e4]; push_cast; ring
  · intro n hn hnp
    obtain ⟨β, hβ, e1⟩ := hu n hn hnp
    refine ⟨?_, β, hβ, e1⟩
    obtain ⟨z', β', hβ', e2⟩ := LaHatMod.exists_int_add_mul n hn hnp ε' hε'
    have hd : (n : ℤ) ∣ u n * z' - 1 := by
      apply IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ ((n : AfP p) * β * β' - β * ε' - ε * β')
        (int_sub (int_sub (int_mul (int_mul (int_natCast n) hβ) hβ') (int_mul hβ hε')) (int_mul hε hβ'))
      have e4 : (u n : AfP p) = ε - (n : AfP p) * β := by rw [e1]; ring
      have e5 : (z' : AfP p) = ε' - (n : AfP p) * β' := by rw [e2]; ring
      push_cast
      rw [e4, e5]
      linear_combination hεε'
    obtain ⟨k, hk⟩ := hd
    exact ⟨z', -k, by linear_combination hk⟩

end GlobalTheory.UnitApprox
