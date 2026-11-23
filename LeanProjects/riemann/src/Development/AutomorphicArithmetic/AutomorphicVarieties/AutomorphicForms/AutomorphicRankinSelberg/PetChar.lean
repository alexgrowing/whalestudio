import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

theorem UpperTheory.V.Af.Rs.petChar :
    UpperTheory.V.Af.Rs.PetChar := by
  intro k L _ χ ψ f g hf hg γ hγ z
  have h := UpperHalfPlane.petersson_slash_SL (k : ℤ) g f γ z
  rw [hg γ hγ, hf γ hγ] at h
  rw [← h]
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply,
    MulChar.star_apply', MulChar.mul_apply]
  ring
