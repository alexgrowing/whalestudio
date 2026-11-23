import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow

noncomputable section

open scoped BigOperators
open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace SumOrbCW

theorem iotaH_bijective (e : ℕ) : Function.Bijective (iotaH e) := by
  obtain ⟨-, hcard, hord, -⟩ := Formalism.TwoAdicCyclotomicDecomposition.quotCyclic e
  have : NeZero (2 ^ e) := ⟨by positivity⟩
  have hinj : Function.Injective (iotaH e) := by
    intro a b hab
    have ha : a.val < orderOf (hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2))) := by
      rw [show hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) = QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
        (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) from rfl, hord]; exact ZMod.val_lt a
    have hb : b.val < orderOf (hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2))) := by
      rw [show hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) = QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
        (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2)) from rfl, hord]; exact ZMod.val_lt b
    exact ZMod.val_injective _ (pow_injOn_Iio_orderOf ha hb hab)
  refine hinj.bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_zmod]

theorem plGG_bijective (D : D7) :
    Function.Bijective (fun z : Bool × HH D => (⟨plGG D z, plGG_mem_Psi D z⟩ : D.R.Psi)) := by
  have hi := D.R.toFrame.iota_bijective
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h' := congrArg Subtype.val h
    cases b <;> cases b' <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h' <;> simp [hi.1 h']
  · rintro ⟨⟨⟨s, c⟩, h⟩, hg⟩
    have hc : c = 1 := hg
    subst hc
    obtain ⟨t, ht⟩ := hi.2 h
    rcases Int.units_eq_one_or s with hs | hs
    · exact ⟨(false, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau1, ht]⟩
    · exact ⟨(true, t), by subst hs; simp [plGG, Formalism.HC.Frame.tau2, ht]⟩

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) :=
  D.eTau.symm.bijective.comp (plGG_bijective D)

theorem sum_wPl (D : D7) (j : ℕ) : (∑ z : Bool × HH D, wPl D j z) = ∑ τ : D.what₂.Tau, wj D j τ :=
  (tauPl_bijective D).sum_comp (wj D j)

end SumOrbCW

end
