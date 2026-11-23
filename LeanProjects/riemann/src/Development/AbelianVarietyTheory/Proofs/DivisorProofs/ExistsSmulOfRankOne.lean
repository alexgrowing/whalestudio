import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM Polynomial

theorem dvd_of_smul_end_eq_smul {R M : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] (f : Module.End R M) {a b : R} (ha : a ≠ 0)
    (h : ∀ x, a • f x = b • x) {x₀ : M} (hx₀ : x₀ ≠ 0) : a ∣ b := by
  obtain ⟨P, hP, hf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (i : ℕ) (x : M), a ^ i • (f ^ i) x = b ^ i • x := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ f, Module.End.mul_apply, pow_succ' a, mul_smul, ih, smul_comm, h, pow_succ, mul_smul]
  have h0 : (P.scaleRoots a).eval b = 0 := by
    have h1 : (P.scaleRoots a).eval b • x₀ = a ^ P.natDegree • (aeval f P) x₀ := by
      rw [eval_eq_sum_range, aeval_eq_sum_range, natDegree_scaleRoots, Finset.sum_smul, LinearMap.sum_apply,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [coeff_scaleRoots, mul_smul, ← hpow, LinearMap.smul_apply, smul_smul, smul_smul, mul_assoc,
        pow_sub_mul_pow a hi', mul_comm]
    rw [hf, LinearMap.zero_apply, smul_zero, smul_eq_zero] at h1
    exact h1.resolve_right hx₀
  let K := FractionRing R
  have ha' : algebraMap R K a ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hc : algebraMap R K a * (algebraMap R K b / algebraMap R K a) = algebraMap R K b :=
    mul_div_cancel₀ _ ha'
  have hint : _root_.IsIntegral R (algebraMap R K b / algebraMap R K a) := by
    refine ⟨P, hP, ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := P) (algebraMap R K) (algebraMap R K b / algebraMap R K a) a
    rw [hc, eval₂_at_apply, h0, map_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (pow_ne_zero _ ha')
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨g, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hg, hc]

theorem exists_smul_of_rank_one (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (h : D.p + D.q = 1) (γ : D.La →+ D.La) (hγ : ∀ (s : 𝓞 E) (x : D.La), γ (s • x) = s • γ x) :
    ∃ g : 𝓞 E, ∀ x, γ x = g • x := by
  have := D.fin
  have := D.proj
  have hr : Module.finrank (𝓞 E) D.La = 1 := D.rank.trans h
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : D.La)
  obtain ⟨a, b, ha, hab⟩ := CMLat.exists_smul_eq_smul hr hx₀ (γ x₀)
  have key : ∀ x, a • γ x = b • x := fun x => by
    obtain ⟨r, s, hr0, e⟩ := CMLat.exists_smul_eq_smul hr hx₀ x
    have h1 : r • (a • γ x - b • x) = 0 := by
      rw [smul_sub, smul_comm r a, ← hγ, e, hγ, smul_comm a s, hab, smul_comm r b, e, smul_comm s b, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hr0)
  let f : Module.End (𝓞 E) D.La := { toFun := γ, map_add' := γ.map_add, map_smul' := hγ }
  obtain ⟨g, rfl⟩ := dvd_of_smul_end_eq_smul f ha key hx₀
  refine ⟨g, fun x => ?_⟩
  have h1 : a • (γ x - g • x) = 0 := by rw [smul_sub, key, mul_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left ha)

end GlobalTheory.FlatCM

end
