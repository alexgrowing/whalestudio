import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_cast_ne_zero_of_field (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  refine ⟨l, hlp, fun h => ?_⟩
  rw [CharP.cast_eq_zero_iff k (ringChar k)] at h
  rcases hlp.eq_one_or_self_of_dvd _ h with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem minpoly_int_coeff_zero_ne_zero {F : Type} [Field F] [NumberField F] (x : 𝓞 F) (hx : x ≠ 0) :
    (minpoly ℤ x).coeff 0 ≠ 0 := by
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.of_finite ℚ (x : F)) hxF
  have h2 : minpoly ℚ (x : F) = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ F hi
  rw [h2, coeff_map] at h1
  intro h; exact h1 (by rw [h, map_zero])

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natAbs_eq_minpoly_coeff_zero_pow {F : Type} [Field F] [NumberField F] (x : 𝓞 F) :
    ∃ r : ℕ, r * (minpoly ℤ x).natDegree = Module.finrank ℚ F ∧
      (Algebra.norm ℤ x).natAbs = ((minpoly ℤ x).coeff 0).natAbs ^ r := by
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow x
  have hm : (minpoly ℤ x).Monic := minpoly.monic (RingOfIntegers.isIntegral x)
  refine ⟨r, ?_, ?_⟩
  · rw [← ReciprocityTheory.ChartRestriction.T1.lat_cp_natDegree x, hr, hm.natDegree_pow]
  · have e : Algebra.norm ℤ x = (-1) ^ Module.finrank ℤ (𝓞 F) * (ReciprocityTheory.ChartRestriction.T1.lat_cp x).coeff 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]; rfl
    rw [e, hr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow]
    simp

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem deg_eq_coeff_zero_pow_of_aeval {k : Type} [Field k] (A : AbVar k) (f : End A) (m : ℤ[X]) (hm : m.Monic)
    (hp : Prime m) (hf : aeval f m = 0) :
    ∃ e : ℕ, e * m.natDegree = 2 * A.dim ∧ (deg (A := A) (B := A) f : ℤ) = m.coeff 0 ^ e := by
  obtain ⟨l, hl, hl0⟩ := exists_prime_cast_ne_zero_of_field k
  haveI := Fact.mk hl
  obtain ⟨-, -, -, hfin, hrank⟩ := GlobalTheory.AV.AbVar.tl_free_finrank k l hl0 A
  haveI := hfin
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.endCharpoly_tate_det_degree_trace k l hl0 A f
  have h1' := @h1 hfin
  have inj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
  let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
    (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)
  have hψ : ψ f = vmap l (A := A) (B := A) f := rfl
  have hT : aeval (vmap l (A := A) (B := A) f) m = 0 := by
    rw [← hψ]
    have := Polynomial.hom_eval₂ m (algebraMap ℤ (End A)) ψ f
    rw [← aeval_def, hf, map_zero, Subsingleton.elim (ψ.comp (algebraMap ℤ (End A))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l (A := A) (B := A) f) (m.map (algebraMap ℤ ℚ_[l]))
    (by rw [aeval_map_algebraMap]; exact hT)
  rw [← h1', ← Polynomial.map_pow] at hdvd
  have hQm : (charpoly f).Monic :=
    Polynomial.monic_of_injective inj (by rw [h1']; exact LinearMap.charpoly_monic _)
  rw [map_dvd_map _ inj hQm] at hdvd
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp _).1 hdvd
  have hQ : charpoly f = m ^ i := eq_of_monic_of_associated hQm (hm.pow i) hi
  have hdeg : (charpoly f).natDegree = 2 * A.dim := by
    rw [← Polynomial.natDegree_map_eq_of_injective inj, h1', LinearMap.charpoly_natDegree, hrank]
  refine ⟨i, ?_, ?_⟩
  · rw [← hdeg, hQ, hm.natDegree_pow]
  · have e := LinearMap.det_eq_sign_charpoly_coeff (vmap l (A := A) (B := A) f)
    rw [h3, ← h1', coeff_map, hrank, pow_mul, neg_one_sq, one_pow, one_mul, hQ, coeff_zero_eq_eval_zero,
      eval_pow, ← coeff_zero_eq_eval_zero] at e
    apply Int.cast_injective (α := ℚ_[l])
    rw [Int.cast_natCast, e, eq_intCast, Int.cast_pow]

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_and_deg_eq_norm_pow : ∀ (k : Type) [Field k] (A : AbVar k) (F : Type) [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (d : ℕ), 2 * A.dim = d * Module.finrank ℚ F → ∀ x : 𝓞 F, x ≠ 0 →
      IsIsogeny (A := A) (B := A) (ι x) ∧ deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
  intro k _ A F _ _ ι d hd x hx
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hm : (minpoly ℤ x).Monic := minpoly.monic hi
  have hp : Prime (minpoly ℤ x) := (minpoly.irreducible hi).prime
  have hf : aeval (ι x) (minpoly ℤ x) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℤ x) (algebraMap ℤ (𝓞 F)) ι x
    rw [← aeval_def, minpoly.aeval, map_zero, Subsingleton.elim (ι.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  obtain ⟨e, he, hdeg⟩ := deg_eq_coeff_zero_pow_of_aeval A (ι x) (minpoly ℤ x) hm hp hf
  obtain ⟨r, hr, hN⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow x
  have hpos : 0 < (minpoly ℤ x).natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hd, ← hr, mul_assoc]
  have hdeg' : deg (A := A) (B := A) (ι x) = ((minpoly ℤ x).coeff 0).natAbs ^ e := by
    have := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  have hval : deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
    rw [hdeg', hN, ← pow_mul, her, mul_comm]
  refine ⟨?_, hval⟩
  by_contra h
  have h0 : deg (A := A) (B := A) (ι x) = 0 := by
    classical
    unfold deg
    rw [if_neg h]
  rw [hdeg'] at h0
  exact minpoly_int_coeff_zero_ne_zero x hx (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 h0).1)

end GlobalTheory.AV.AbVar
