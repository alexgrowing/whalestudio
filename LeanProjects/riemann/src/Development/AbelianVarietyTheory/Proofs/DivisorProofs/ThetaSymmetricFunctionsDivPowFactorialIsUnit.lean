import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPropeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  intro k Ω _ _ _ A _ N c a j hca hcb hj hjb
  have hpow : c a ^ N.factorial ≠ 0 := pow_ne_zero _ hca
  let d : Fin N → A := fun b => ⟨c b / c a, hcb b⟩
  have hd : ∀ j' : Fin N, symTup c j' / c a ^ N.factorial = ((symTup d j' : A) : Ω) := by
    intro j'
    have h1 : c = fun b => c a * ((d b : A) : Ω) := by
      funext b; show c b = c a * (c b / c a); field_simp
    have h2 := (GlobalTheory.UMin.symTup_basic).1 Ω N (fun b => ((d b : A) : Ω)) (c a) j'
    have h3 := (GlobalTheory.UMin.symTup_basic).2.2.1 A Ω A.val.toRingHom N d j'
    have h4 : symTup c j' = c a ^ N.factorial * symTup (fun b => ((d b : A) : Ω)) j' := by
      rw [← h2, ← h1]
    rw [h4, mul_div_cancel_left₀ _ hpow]
    exact h3.symm
  have hda : d a = 1 := Subtype.ext (by show c a / c a = 1; exact div_self hca)
  obtain ⟨k0, hk1, hk2, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one A (Fin N) d a hda
  rw [Fintype.card_fin] at hk2
  let j' : Fin N := ⟨k0 - 1, by omega⟩
  have hk0 : (j' : ℕ) + 1 = k0 := by show k0 - 1 + 1 = k0; omega
  have hu : IsUnit (symTup d j') := by
    unfold symTup; rw [hk0]; exact hku.pow _
  let x : A := ⟨symTup c j / c a ^ N.factorial, by rw [hd j]; exact (symTup d j).2⟩
  let z : A := ⟨symTup c j' / symTup c j, hjb j'⟩
  have hxz : symTup d j' = x * z := by
    apply Subtype.ext
    show ((symTup d j' : A) : Ω) = (symTup c j / c a ^ N.factorial) * (symTup c j' / symTup c j)
    rw [← hd j']
    field_simp
  rw [hxz] at hu
  have hx : IsUnit x := isUnit_of_mul_isUnit_left hu
  refine ⟨div_ne_zero hj hpow, x.2, ?_⟩
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  have hv' : (symTup c j / c a ^ N.factorial) * (v : Ω) = 1 := by
    have := congrArg (fun t : A => (t : Ω)) hv
    simpa using this
  rw [← eq_inv_of_mul_eq_one_right hv']
  exact v.2
