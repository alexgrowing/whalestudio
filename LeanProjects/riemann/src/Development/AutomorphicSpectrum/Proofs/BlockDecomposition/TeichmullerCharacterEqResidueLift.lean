import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem isUnit_BdRp_of_thB {l : ℕ} [Fact l.Prime] {u : Formalism.Per6.BdRp l} (h : thB l u ≠ 0) :
    IsUnit u := by
  change IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)
  by_contra hy
  have h2 := (IsLocalRing.mem_maximalIdeal _).2 hy
  rw [GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h2
  exact h h2

theorem eq_of_pow_eq_self_of_thB_eq {l : ℕ} [Fact l.Prime] {q : ℕ} (hq : 2 ≤ q)
    {a b : Formalism.Per6.BdRp l} (ha : a ^ q = a) (hb : b ^ q = b) (hab : thB l a = thB l b) :
    a = b := by
  set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS
  have hkey : (a - b) * (S - 1) = 0 := by
    have h1 : (a - b) * S = a ^ q - b ^ q := (Commute.all a b).mul_geom_sum₂ q
    rw [mul_sub, h1, ha, hb, mul_one, sub_self]
  have hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]
    · simp
    · intro i hi
      have hi' : i ≤ q - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      rw [map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']
  have hζ : thB l a ^ q = thB l a := by rw [← map_pow, ha]
  have hne : thB l (S - 1) ≠ 0 := by
    rw [map_sub, map_one, hθS]
    by_cases h0 : thB l a = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h1 : thB l a ^ (q - 1) = 1 := by
        have e : thB l a ^ (q - 1) * thB l a = 1 * thB l a := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
        exact mul_right_cancel₀ h0 e
      rw [h1, mul_one, sub_ne_zero]
      exact_mod_cast (by omega : q ≠ 1)
  have hu := isUnit_BdRp_of_thB hne
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)

theorem tch_eq_rB_of_sh_eq : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  intro l _ q hq _ x y hx hy hxy
  refine eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_
  · rw [← tch_pow, hx]
  · rw [← map_pow, hy]
  · rw [thB_tch, thB_rB, hxy, omC_apply]

end GlobalTheory.CompanionTheory.LTPer.Tilt
