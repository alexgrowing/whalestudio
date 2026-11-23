import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogMulPf

def ratHom {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) : ℚ →+* S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom S) (fun y => by
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h := hu _ (Int.natAbs_ne_zero.2 hy)
    rcases Int.natAbs_eq (y : ℤ) with e | e
    · rw [e]; simpa using h
    · rw [e]; simpa using h)

theorem inv_smul_eq {S : Type} [CommRing S] [Algebra ℚ S] (m : ℕ) (hm : m ≠ 0) (x : S) :
    ((m : ℚ)⁻¹) • x = Ring.inverse (m : S) * x := by
  have h1 : (m : S) * algebraMap ℚ S (m : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ S), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]
  have h : IsUnit (m : S) := IsUnit.of_mul_eq_one _ h1
  apply h.mul_left_cancel
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, h1, Ring.mul_inverse_cancel _ h]

theorem core (hLA : LogAlg) {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) (T : Subring S) (x y : S)
    (hx : ∀ k : ℕ, Ring.inverse (k.factorial : S) * x ^ k ∈ T)
    (hy : ∀ k : ℕ, Ring.inverse (k.factorial : S) * y ^ k ∈ T) :
    (∀ k : ℕ, Ring.inverse (k.factorial : S) * (x + y + x * y) ^ k ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) *
          (Ring.inverse ((k + 1).factorial : S) * (x + y + x * y) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * x ^ (k + 1)) +
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * y ^ (k + 1)) +
          (N.factorial : S) * c := by
  letI : Algebra ℚ S := (ratHom hu).toAlgebra
  have e : ∀ (k : ℕ) (z : S), ((k.factorial : ℚ)⁻¹) • z ^ k = Ring.inverse (k.factorial : S) * z ^ k :=
    fun k z => inv_smul_eq _ k.factorial_ne_zero _
  have := hLA S T (fun k z => ((k.factorial : ℚ)⁻¹) • z ^ k) (fun _ _ => rfl) x y
    (fun k => by simp only [e]; exact hx k) (fun k => by simp only [e]; exact hy k)
  simpa only [e] using this

theorem sum_eq_of_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (T : Subalgebra R S) (f f' f'' : ℕ → T)
    (N : ℕ) (c : T)
    (e : ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f'' (k + 1) : S) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f (k + 1) : S) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f' (k + 1) : S) + (N.factorial : S) * (c : S)) :
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f'' (k + 1) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f (k + 1) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f' (k + 1) + (N.factorial : T) * c := by
  apply Subtype.ext
  push_cast
  exact e

variable {l : ℕ} [Fact l.Prime]

theorem factorial_acr (A : PAlg l) (n : ℕ) : (((l * n).factorial : ℕ) : A.Acr n) = 0 := by
  obtain ⟨d, hd⟩ := ACris.pow_dvd_factorial (p := l) (le_refl (l * n))
  rw [hd, Nat.cast_mul, Nat.cast_pow, A.pow_l_acr, zero_mul]

theorem isLog_mul (hLA : LogAlg) (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n)
    (hy : IsLog A n w y) (hy' : IsLog A n w' y') : IsLog A n (w * w') (y + y') := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have hab : algebraMap A.W (WL l A.A) (w * w' - 1) =
      algebraMap A.W (WL l A.A) (w - 1) + algebraMap A.W (WL l A.A) (w' - 1) +
        algebraMap A.W (WL l A.A) (w - 1) * algebraMap A.W (WL l A.A) (w' - 1) := by
    simp only [map_sub, map_mul, map_one]; ring
  obtain ⟨hT, hN⟩ := core hLA (fun m hm => A.isUnit_natCast hm) A.Acr0.toSubring
    (algebraMap A.W (WL l A.A) (w - 1)) (algebraMap A.W (WL l A.A) (w' - 1))
    (fun k => by have h := (g k).2; rw [hg k] at h; exact h)
    (fun k => by have h := (g' k).2; rw [hg' k] at h; exact h)
  have hmem : ∀ k, dpw k (w * w' - 1) ∈ A.Acr0 := fun k => by
    rw [dpw, hab]; exact hT k
  obtain ⟨c, hc, e⟩ := hN (l * n)
  refine ⟨fun k => ⟨dpw k (w * w' - 1), hmem k⟩, fun _ => rfl, ?_⟩
  have e0 := sum_eq_of_coe A.Acr0 g g' (fun k => ⟨dpw k (w * w' - 1), hmem k⟩) (l * n) ⟨c, hc⟩ (by
    simp only [hg, hg']
    simp only [dpw, hab]
    exact e)
  have e1 := congrArg (A.mkAcr n) e0
  simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at e1
  rw [e1, factorial_acr, zero_mul, add_zero]

theorem logMul : CrystallineSemistableComparison.E.LogAlg → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul :=
  fun h _ _ _ A n w w' y y' _ _ hy hy' => isLog_mul h A n w w' y y' hy hy'

end GlobalTheory.CompanionTheory.LogMulPf
