import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodular
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.LevelRed

open GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem mk_eq_iff (h𝔪 : 𝔪 ≠ ⊥) (r b : 𝓞 D.host.E) :
    Ideal.Quotient.mk 𝔪 r = Ideal.Quotient.mk 𝔪 b ↔
      inc D (r : D.host.E) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  have e : inc D (r : D.host.E) - inc D (b : D.host.E) = inc D ((r - b : 𝓞 D.host.E) : D.host.E) := by
    push_cast
    rw [map_sub]
  rw [Ideal.Quotient.eq, e]
  constructor
  · intro h
    simpa using gen_mem_hatId D 𝔪 h (one_mem (OhE D))
  · intro h
    obtain ⟨c, hc, e'⟩ := (FractionalIdeal.mem_coeIdeal _).1 (GlobalTheory.HeisTranslate.mem_of_inc_mem_hatId h𝔪 h)
    have : c = r - b := RingOfIntegers.coe_injective e'
    exact this ▸ hc

theorem exists_redHom (h𝔪 : 𝔪 ≠ ⊥) : ∃ red : OhE D →+* 𝓞 D.host.E ⧸ 𝔪, ∀ (x : OhE D) (b : 𝓞 D.host.E),
    red x = Ideal.Quotient.mk 𝔪 b ↔ (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  choose r hr using fun x : OhE D => exists_red D 𝔪 h𝔪 (x : AE D) x.2
  have key : ∀ (x : OhE D) (b : 𝓞 D.host.E), Ideal.Quotient.mk 𝔪 (r x) = Ideal.Quotient.mk 𝔪 b ↔
      (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
    intro x b
    rw [mk_eq_iff D 𝔪 h𝔪]
    constructor
    · intro h
      have := add_mem (hr x) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hr x)
      rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := fun x => Ideal.Quotient.mk 𝔪 (r x)
            map_one' := ?_
            map_mul' := fun x y => ?_
            map_zero' := ?_
            map_add' := fun x y => ?_ }, key⟩
  · rw [← map_one (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_mul, key]
    have := add_mem (mul_mem_hatId D 𝔪 y.2 (hr x))
      (mul_mem_hatId D 𝔪 (VacMove.inc_int D (r x)) (hr y))
    convert this using 1
    push_cast
    rw [map_mul]
    ring
  · rw [← map_zero (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_add, key]
    have := add_mem (hr x) (hr y)
    convert this using 1
    push_cast
    rw [map_add]
    ring

def intMat (N : ℕ) : ↥(intG D N) →* Matrix (Fin N) (Fin N) (OhE D) where
  toFun k := Matrix.of fun i j =>
    ⟨(((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j, (((mem_intG _).1 k.2) i j).1⟩
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  map_mul' x y := by
    ext i j
    simp [Matrix.mul_apply]

theorem exists_levelRed : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  intro D 𝔪 h𝔪 N
  obtain ⟨red, hred⟩ := exists_redHom D 𝔪 h𝔪
  exact ⟨((red.mapMatrix (m := Fin N)).toMonoidHom.comp (intMat D N)).toHomUnits,
    fun k i j b => hred (intMat D N k i j) b⟩

end GlobalTheory.LevelRed

end
