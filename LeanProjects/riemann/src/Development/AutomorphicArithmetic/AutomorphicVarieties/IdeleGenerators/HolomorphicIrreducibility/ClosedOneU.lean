import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NotDvdMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolEis
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime]

private theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

private theorem norm_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : Qbar l)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at h2

private def oneU (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : ((a * b : (Qbar l)ˣ) : Qbar l) - 1 = a * (b - 1) + (a - 1) := by rw [Units.val_mul]; ring
    show ‖_‖ < 1
    rw [e]
    refine add_lt ?_ ha
    rw [norm_mul, norm_one_of ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    have e : (a : Qbar l) * (((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(a - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_one_of ha, one_mul, norm_neg] at h
    show ‖_‖ < 1
    rw [h]
    exact ha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
private theorem cyc_mem (s : G F Ω) : cycBar F Ω l s ^ (l - 1) ∈ oneU l := by
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - 1 =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l])) ^ _ - 1 = _
    simp
  show ‖_‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

end SlopeTestRemainingChoices
