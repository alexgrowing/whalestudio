import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory
open Matrix

theorem exists_e8Form_value_not_dvd_prime (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (p : ℕ) (hp : p.Prime) :
    ∃ ε : Fin 8 → ℤ, ¬ (p : ℤ) ∣ ∑ u, ∑ v, W u v * ε u * ε v := by
  by_contra h
  push_neg at h
  have hQ : ∀ ε : Fin 8 → ℤ, ∑ u, ∑ v, W u v * ε u * ε v = ε ⬝ᵥ (W *ᵥ ε) := by
    intro ε
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hA : ∀ i j, (p : ℤ) ∣ (W + W.transpose) i j := by
    intro i j
    have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1)
    have h3 := h (Pi.single j 1)
    rw [hQ] at h1 h2 h3
    have e : (Pi.single i 1 + Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single j 1) = (W + W.transpose) i j := by
      simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
        single_dotProduct]
      ring
    rw [← e]
    exact dvd_sub (dvd_sub h1 h2) h3
  set A := W + W.transpose
  have hB : A = (p : ℤ) • Matrix.of (fun i j => A i j / p) := by
    ext i j
    simp [Int.mul_ediv_cancel' (hA i j)]
  have hdet : A.det = 1 := hW.2
  rw [hB, Matrix.det_smul] at hdet
  have : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by simp)) _
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem exists_e8Form_value_coprime_oddPrimePow' : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 →
    ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  intro W hW p k hp hp2
  obtain ⟨ε, hε⟩ := exists_e8Form_value_not_dvd_prime W hW p hp
  refine ⟨ε, ?_⟩
  rw [← pow_mul]
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hε (Int.natCast_dvd.2 hd)

end GlobalTheory
