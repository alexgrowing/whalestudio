import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.ZUSum

open scoped NNReal

theorem term_identity (q : ℕ) (hq : q ≠ 0) (r : ℂ) (hr : r = ((NNReal.sqrt (q : ℝ≥0) : ℝ) : ℂ))
    (s : ℂ) (m n : ℕ) :
    (q : ℂ) ^ (-((m : ℤ) + (n : ℤ))) * r ^ (-(m : ℤ)) * ((q : ℂ) ^ (-(m : ℂ) * (s - 3 / 2))) *
        ((q : ℂ) ^ (-(n : ℂ) * (2 * s - 1))) = ((q : ℂ) ^ (-s)) ^ (m + 2 * n) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hr2 : r = Complex.exp (Complex.log (q : ℂ) / 2) := by
    have h1 : ((NNReal.sqrt (q : ℝ≥0) : ℝ)) = Real.exp (Real.log (q : ℝ) / 2) := by
      rw [Real.coe_sqrt, Real.exp_half, Real.exp_log hpos]
      simp
    rw [hr, h1, Complex.ofReal_exp, Complex.ofReal_div, Complex.natCast_log]
    simp
  have hqe : ∀ k : ℤ, (q : ℂ) ^ k = Complex.exp ((k : ℂ) * Complex.log (q : ℂ)) := by
    intro k
    rw [Complex.exp_int_mul, Complex.exp_log hq']
  rw [hr2, hqe, ← Complex.exp_int_mul, Complex.cpow_def_of_ne_zero hq', Complex.cpow_def_of_ne_zero hq',
    Complex.cpow_def_of_ne_zero hq', ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zU_eq_of_hasSum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (S S' : ℤ → ℤ → ℂ) (s R : ℂ), (∀ a b : ℤ, W (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * S a b else 0) → (∀ a b : ℤ, W' (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * S' a b else 0) → HasSum (fun p : ℕ × ℕ => S ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * S' ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * ((residueCard F : ℂ) ^ (-s)) ^ (p.1 + 2 * p.2)) R → zU W W' s = R := by
  intro F _ _ _ _ W W' S S' s R hW hW' hS
  have hinj : Function.Injective (fun p : ℕ × ℕ => (((p.1 : ℤ), (p.2 : ℤ)) : ℤ × ℤ)) := by
    intro p p' h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  unfold zU
  refine HasSum.tsum_eq ((hinj.hasSum_iff ?_).1 ?_)
  · intro p hp
    have hneg : ¬ (0 ≤ p.1 ∧ 0 ≤ p.2) := by
      rintro ⟨h1, h2⟩
      refine hp ⟨(p.1.toNat, p.2.toNat), ?_⟩
      simp [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    have hc : ¬ (p.2 ≤ p.1 + p.2 ∧ 0 ≤ p.2) := by
      rintro ⟨h1, h2⟩
      exact hneg ⟨by omega, h2⟩
    rw [hW, if_neg hc]
    simp
  · convert hS using 2 with p
    obtain ⟨m, n⟩ := p
    have h1 : ((n : ℤ) ≤ (m : ℤ) + (n : ℤ) ∧ (0 : ℤ) ≤ (n : ℤ)) := by omega
    have h2 : (n : ℤ) ≤ (m : ℤ) + (n : ℤ) := by omega
    have hid := term_identity (residueCard F) GroundTheory.LocalField.residueCard_ne_zero (Spherical.sqrtQ F) rfl s m n
    have hsub : (m : ℤ) + (n : ℤ) - (n : ℤ) = (m : ℤ) := by ring
    simp only [Function.comp_apply]
    rw [hW, hW', if_pos h1, if_pos h2, hsub, ← hid]
    push_cast
    ring

end GlobalTheory.CompanionTheory.GL2Factorization.ZUSum
