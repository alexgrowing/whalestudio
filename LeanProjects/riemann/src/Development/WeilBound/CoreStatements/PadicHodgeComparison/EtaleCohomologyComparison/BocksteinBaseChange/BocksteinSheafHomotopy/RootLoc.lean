import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem cyc_pow (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∀ a : ℕ, expand ℤ (p ^ a) (cyclotomic (p ^ b) ℤ) = cyclotomic (p ^ (a + b)) ℤ
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ', expand_mul, cyc_pow p b hp hb a,
      cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (by omega : a + b ≠ 0))]
    congr 1
    rw [← pow_succ]
    congr 1
    omega

theorem rootLoc (p a b : ℕ) [Fact p.Prime] (hb : 0 < b) (U : Scheme.{0}) (ξ : Prim (p ^ b) Γ(U, ⊤)) :
    Loc U fun V g => ∃ ζ : Prim (p ^ (a + b)) Γ(V, ⊤), ζ.1 ^ (p ^ a) = g.appTop.hom ξ.1 := by
  have hp : p.Prime := Fact.out
  have hpU : IsUnit (p : Γ(U, ⊤)) := by
    have h := ξ.2.1
    rw [Nat.cast_pow] at h
    exact (isUnit_pow_iff hb.ne').1 h
  have hξ1 : ξ.1 ^ (p ^ b) = 1 := by
    obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one (p ^ b) ℤ
    have := congrArg (aeval ξ.1) hh
    rw [map_mul, ξ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hξu : IsUnit ξ.1 := by
    refine isUnit_iff_exists_inv.2 ⟨ξ.1 ^ (p ^ b - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)), hξ1]
  obtain ⟨S, hS, hP⟩ := kumLoc U (p ^ a) hξu.unit (by rw [Nat.cast_pow]; exact hpU.pow _)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, hv⟩ := hP V g hg
  rw [IsUnit.unit_spec] at hv
  have hpV : IsUnit (p : Γ(V, ⊤)) := by simpa using hpU.map g.appTop.hom
  refine ⟨⟨v, by rw [Nat.cast_pow]; exact hpV.pow _, ?_⟩, hv⟩
  rw [← cyc_pow p b hp hb a, expand_aeval, hv]
  exact (Prim.map g.appTop.hom ξ).2.2

end CrystallineSemistableComparison.KummerTwistLemmas
