import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasics

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem root_Zp {y : F} (hy : (1 + y) ^ (p ^ m) = 1) : Polynomial.aeval y (Zp (O := O) p m) = 0 := by
  simp only [Zp, map_sub, map_pow, map_add, map_one, Polynomial.aeval_X, hy, sub_self]

theorem evR_congr {x x' : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hx' : Polynomial.aeval x' (Zp (O := O) p m) = 0) (h : x = x') (f : PowerSeries O) :
    evR p m hlm hx f = evR p m hlm hx' f := by
  subst h
  rfl

theorem evR_eq_cc {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (hx0 : x = 0)
    (f : PowerSeries O) : evR p m hlm hx f = algebraMap O F (PowerSeries.constantCoeff f) := by
  subst hx0
  obtain ⟨q, hq⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
    ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
  show evP p m 0 f = _
  rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx f q _ hq]
  conv_rhs => rw [hq]
  rw [← Polynomial.coeff_zero_eq_aeval_zero']
  simp [Zs]

theorem evR_onePow {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (k : ℕ) :
    evR p m hlm hx ((1 + PowerSeries.X) ^ k) = (1 + x) ^ k := by
  have hX : evR p m hlm hx PowerSeries.X = x := by
    show evP p m x PowerSeries.X = x
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx PowerSeries.X 0 Polynomial.X (by simp)]
    simp
  rw [map_pow, map_add, map_one, hX]

end SlopeTestRemainingChoices

theorem exists_prim {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (N : ℕ) (hN : 0 < N) :
    ∃ ζ : F, IsPrimitiveRoot ζ N := by
  haveI : NeZero (N : F) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N F) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hN).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
