import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit
import Mathlib
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate
import Formalism.ResultantValuation.ResultantAdjugateProofs.Mobius
import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
import Formalism.ResultantValuation.ResultantAdjugateProofs.Koszul
import Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic
import Formalism.ResultantValuation.BoundedCubic
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem twist_invertible_holds : TwistInvertible := by
  intro k V _ _ _ _ γ₀ c hc hne
  let L : Module.End k V := c⁻¹ • γ₀ - 1
  have hL : ∀ v, L v = c⁻¹ • γ₀ v - v := fun v => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hL, sub_eq_zero] at hv
    have h2 : γ₀ v = c • v := by
      calc γ₀ v = c • (c⁻¹ • γ₀ v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    by_contra hv0
    exact hne (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h2, hv0⟩)
  have hbij : Function.Bijective L := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact hbij

theorem phi15_is_unit_holds : PrimitiveRootFifteenSubOneUnit := by
  intro R _ _ ζ hζ
  have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ 15 := by
    intro p hp k h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ k by rw [h]; norm_num)
    have h5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p ^ k by rw [h]; norm_num)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp h5
    omega
  have hev : (Polynomial.cyclotomic 15 R).eval 1 = 1 := Polynomial.eval_one_cyclotomic_not_prime_pow hnp
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hmem : ζ ∈ primitiveRoots 15 R := (mem_primitiveRoots (by norm_num)).mpr hζ
  have hdvd : (1 - ζ) ∣ 1 := (Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hmem).trans hev.dvd
  have hu : IsUnit (1 - ζ) := isUnit_of_dvd_one hdvd
  rw [show ζ - 1 = -(1 - ζ) by ring]
  exact hu.neg

theorem g5b_multiplicity_holds : UnitEvalOfMultiplicity := by
  intro O _ _ t c s' hs hmult
  have hmap : (s' * (X - C c) ^ t).map (IsLocalRing.residue O) =
      s'.map (IsLocalRing.residue O) * (X - C (IsLocalRing.residue O c)) ^ t := by
    simp
  have hs0 : s'.map (IsLocalRing.residue O) ≠ 0 := (hs.map _).ne_zero
  rw [hmap, Polynomial.rootMultiplicity_mul
    (mul_ne_zero hs0 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.rootMultiplicity_X_sub_C_pow] at hmult
  have h0 : (s'.map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = 0 := by
    omega
  rw [Polynomial.rootMultiplicity_eq_zero_iff] at h0
  have hne : (s'.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O c) ≠ 0 :=
    fun e => hs0 (h0 e)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at hne
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne

theorem same_residue_holds : SameResidue := by
  intro O _ _ X _ T hT a ha x y
  let ev : X → (T →+* IsLocalRing.ResidueField O) := fun z =>
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  have hev : ∀ z (b : T), ev z b = IsLocalRing.residue O ((b : X → O) z) := fun z b => rfl
  have hsurj : ∀ z, Function.Surjective (ev z) := by
    intro z k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap O T r, by rw [hev]; simp⟩
  have hmax : ∀ z, RingHom.ker (ev z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hmem : ((⟨a, ha⟩ : T) - algebraMap O T (a x)) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub, hev, hev]
    simp
  rw [hmax x, ← hmax y, RingHom.mem_ker, map_sub, hev, hev, sub_eq_zero] at hmem
  simpa using hmem.symm

end Formalism.IrreducibleCountingLemmas.Z
