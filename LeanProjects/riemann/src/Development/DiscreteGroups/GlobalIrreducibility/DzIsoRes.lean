import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

theorem norm_symm_le (y : 𝒪[w.adicCompletion E]) : ‖i.symm (y : w.adicCompletion E)‖ ≤ 1 := by
  rw [← norm_le_iff i hi, RingEquiv.apply_symm_apply]
  exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 y.2)

def toIntFun (y : 𝒪[w.adicCompletion E]) : ℤ_[g] := ⟨i.symm y, norm_symm_le i hi y⟩

theorem coe_toIntFun (y : 𝒪[w.adicCompletion E]) : ((toIntFun i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def toInt : 𝒪[w.adicCompletion E] →+* ℤ_[g] where
  toFun := toIntFun i hi
  map_one' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_one]; simp)
  map_mul' a b := PadicInt.ext (by rw [PadicInt.coe_mul, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)
  map_zero' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_zero]; simp)
  map_add' a b := PadicInt.ext (by rw [PadicInt.coe_add, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)

theorem coe_toInt (y : 𝒪[w.adicCompletion E]) : ((toInt i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def redO : 𝒪[w.adicCompletion E] →+* ZMod g := (PadicInt.toZMod (p := g)).comp (toInt i hi)

theorem redO_surjective : Function.Surjective (redO i hi) := by
  intro a
  refine ⟨(a.val : 𝒪[w.adicCompletion E]), ?_⟩
  show PadicInt.toZMod (toInt i hi (a.val : 𝒪[w.adicCompletion E])) = a
  rw [map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem ker_redO : RingHom.ker (redO i hi) = IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := by
  ext y
  rw [← IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_lt, RingHom.mem_ker]
  show PadicInt.toZMod (toInt i hi y) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_toInt, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]

theorem resCard_eq : resCard (w.adicCompletion E) = g := by
  have e : (𝒪[w.adicCompletion E] ⧸ IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (ker_redO i hi).symm).trans (RingHom.quotientKerEquivOfSurjective (redO_surjective i hi))
  show Nat.card (𝒪[w.adicCompletion E] ⧸ IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) = g
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

theorem valuation_i_eq_uniformizer : valuation (w.adicCompletion E) (i (g : ℚ_[g])) = uniformizer (w.adicCompletion E) := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    exact (valuation_lt_iff i hi _).2 Padic.norm_p_lt_one
  · obtain ⟨y, hy⟩ := valuation_surjective (K := w.adicCompletion E) (uniformizer (w.adicCompletion E))
    have hx : ‖i.symm y‖ < 1 :=
      (valuation_lt_iff i hi _).1 (by rw [RingEquiv.apply_symm_apply, hy]; exact uniformizer_lt_one)
    obtain ⟨x', hx'⟩ : ∃ x' : ℤ_[g], (x' : ℚ_[g]) = i.symm y := ⟨⟨i.symm y, hx.le⟩, rfl⟩
    obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd x').1 (by rw [PadicInt.norm_def, hx']; exact hx)
    have e := congrArg (fun z : ℤ_[g] => (z : ℚ_[g])) hc
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast, hx'] at e
    have e2 : y = i (g : ℚ_[g]) * i (c : ℚ_[g]) := by
      rw [← map_mul, ← e, RingEquiv.apply_symm_apply]
    rw [← hy, e2, map_mul]
    exact mul_le_of_le_one_right' ((valuation_le_iff i hi _).2 c.2)

theorem valuation_natCast_eq_uniformizer : valuation (w.adicCompletion E) (g : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
  rw [← map_natCast i g, valuation_i_eq_uniformizer i hi]

end DiscreteGroups.sglob.DzIso
