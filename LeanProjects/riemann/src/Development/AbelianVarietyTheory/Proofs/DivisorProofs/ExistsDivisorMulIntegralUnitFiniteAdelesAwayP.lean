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

namespace GlobalTheory.AfUnitSplit

theorem isInt_add' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_mul' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isInt_intCast' {p : ℕ} (k : ℤ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ k

theorem exists_dvd_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a →
    IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧
      ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  intro p _ a b K hK hKp ha hb hab
  obtain ⟨m₀, β, hβ, e⟩ := LaHatMod.exists_int_add_mul K hK hKp a ha
  have hgpos : 0 < Int.gcd m₀ (K : ℤ) := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hK.ne')
  obtain ⟨g, a₀, K₀, hg, hcop, hm, hKe⟩ := Int.exists_gcd_one' hgpos
  have hgK : g ∣ K := by
    have : (g : ℤ) ∣ (K : ℤ) := ⟨K₀, by rw [hKe]; ring⟩
    exact_mod_cast this
  have hgp : g.Coprime p := Nat.Coprime.coprime_dvd_left hgK hKp
  have hbez : (1 : ℤ) = a₀ * Int.gcdA a₀ K₀ + K₀ * Int.gcdB a₀ K₀ := by
    rw [← Int.gcd_eq_gcd_ab, hcop]; rfl
  set s := Int.gcdA a₀ K₀
  set t := Int.gcdB a₀ K₀
  have hbez' : (1 : AfP p) = (a₀ : AfP p) * s + (K₀ : AfP p) * t := by
    have := congrArg (Int.cast : ℤ → AfP p) hbez; push_cast at this; exact this
  have hKc : (K : AfP p) = (K₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hKe; push_cast at this; exact this
  have hmc : (m₀ : AfP p) = (a₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hm; push_cast at this; exact this
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  set u := algebraMap ℚ (AfP p) (g : ℚ)⁻¹
  have hu : (g : AfP p) * u = 1 := by
    rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hgq, map_one]
  have ha' : a = (g : AfP p) * ((a₀ : AfP p) + (K₀ : AfP p) * β) := by
    rw [e, hmc, hKc]; ring
  have hεb : ((a₀ : AfP p) + (K₀ : AfP p) * β) * b = (K₀ : AfP p) := by
    linear_combination (-(((a₀ : AfP p) + (K₀ : AfP p) * β) * b - (K₀ : AfP p))) * hu + u * hab
      - u * b * ha' + u * hKc
  refine ⟨g, (a₀ : AfP p) + (K₀ : AfP p) * β, (s : AfP p) - b * ((s : AfP p) * β - t), hgp, hgK,
    isInt_add' (isInt_intCast' _) (isInt_mul' (isInt_intCast' _) hβ),
    isInt_sub' (isInt_intCast' _) (isInt_mul' hb (isInt_sub' (isInt_mul' (isInt_intCast' _) hβ) (isInt_intCast' _))),
    ?_, ha'⟩
  linear_combination (-((s : AfP p) * β - t)) * hεb - hbez'

end GlobalTheory.AfUnitSplit
