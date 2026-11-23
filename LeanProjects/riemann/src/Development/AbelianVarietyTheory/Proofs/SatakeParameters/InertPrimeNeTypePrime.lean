import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertNotType

theorem main : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  intro D l k h heq
  subst heq
  have h1 := D.ntypes.g_cond k
  have hdvd : 4 * D.host.d ∣ D.host.QS * D.host.q * D.host.d :=
    Nat.mul_dvd_mul_right (((by decide : 4 ∣ 16).trans D.host.sixteen_dvd_QS).mul_right _) _
  have hd1 : D.host.g k % (4 * D.host.d) = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) hdvd, h1]
    exact Nat.mod_eq_of_lt (by have := D.host.hyp.2.1.two_le; omega)
  have h21 : D.host.g k % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k) (⟨2 * D.host.d, by ring⟩ : 2 ∣ 4 * D.host.d), hd1]
  have hodd : Odd (D.host.g k) := Nat.odd_iff.2 h21
  have hJ : jacobiSym (-(D.host.d : ℤ)) (D.host.g k) = 1 := by
    rw [jacobiSym.mod_right _ hodd]
    have : (-(D.host.d : ℤ)).natAbs = D.host.d := by simp
    rw [this, hd1, jacobiSym.one_right]
  unfold TwistedPlaces.InertK Host.cls primeClass at h
  split_ifs at h <;> simp_all

end GlobalTheory.InertNotType
