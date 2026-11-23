import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PlaceBoundOwnPrimeOf

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie

theorem ramLoss_le_vLa_pPow (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ)
    (w : WeightFamilies.Wt D j) (a b : ℕ) (ha : c2 D w ≤ a) (hb : Formalism.MainNotions.DIV.Cons.cHalf w ≤ b) :
    ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  obtain ⟨hs, hq, hd, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  have hN : pPow D a b b ≠ 0 := by
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hqp.ne_zero)) (pow_ne_zero _ hdp.ne_zero)
  have hl := Crude.resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hl⟩
  have ha' : (DF w : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (DF w : ℝ) / 2 ≤ b := Nat.ceil_le.1 hb
  have hD : (0 : ℝ) ≤ (DF w : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ (ramOverZ la : ℝ) := Nat.cast_nonneg _
  have hR : ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) = (padicValNat (resCharOf la) (pPow D a b b) : ℝ) * ramOverZ la := by
    rw [Crude.crv_vLa_natCast la hN, Int.cast_natCast, Nat.cast_mul]
  have hz : ∀ p ∈ D.host.condN.primeFactors, p ≠ resCharOf la →
      ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p * (DF w : ℝ) / 2 = 0 := fun p hp hne => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [Crude.crv_vLa_natCast la hpp.ne_zero, padicValNat_primes hne.symm]; simp
  rw [ramLoss, hR]
  by_cases hm : resCharOf la ∈ D.host.condN.primeFactors
  · rw [Finset.sum_eq_single_of_mem _ hm hz, Crude.crv_vLa_natCast la hl.ne_zero, padicValNat_self]
    have key : D.host.vdH (resCharOf la) * (DF w : ℝ) / 2 ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) := by
      have hv0 := D.host.vdH_nonneg (resCharOf la)
      have hle : ∀ k : ℕ, resCharOf la ^ k ∣ pPow D a b b → (k : ℝ) ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) :=
        fun k hk => by exact_mod_cast (padicValNat_dvd_iff_le hN).1 hk
      rcases (D.host.dvd_condN_iff_small hl).1 (Nat.dvd_of_mem_primeFactors hm) with h | h | h
      · have h1 := hle (padicValNat (resCharOf la) D.host.QS * a) (by
          rw [pow_mul]; exact ((pow_dvd_pow_of_dvd pow_padicValNat_dvd a).mul_right _).mul_right _)
        have h2 := (hs _ h).1
        push_cast at h1
        nlinarith [mul_le_mul h2 ha' hD (Nat.cast_nonneg _), mul_nonneg hv0 hD]
      · have h1 := hle b (by rw [h]; exact (Dvd.intro_left _ rfl).mul_right _)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hq hD]
      · have h1 := hle b (by rw [h]; exact Dvd.intro_left _ rfl)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hd hD]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right key he]
  · rw [Finset.sum_eq_zero fun p hp => hz p hp fun h => hm (h ▸ hp)]
    positivity

end GlobalTheory.PlaceTop
