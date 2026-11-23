import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicRatCharPolyAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharpolyOfMonicIntegralAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_natCast_ne_zero_of_field (K : Type) [Field K] : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨3, Nat.prime_three, ?_⟩
    intro h3
    have : (1 : K) = 0 := by
      have e : (1 : K) = (3 : ℕ) - (2 : K) := by push_cast; ring
      rw [e, h3, h2, sub_zero]
    exact one_ne_zero this
  · exact ⟨2, Nat.prime_two, by exact_mod_cast h2⟩

noncomputable def vendRing {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) : End A →+* Module.End ℚ_[l] (Vl l A) :=
  (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)

theorem vendRing_apply {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) (f : End A) : vendRing l A f = vmap l f := rfl

theorem exists_isCharpoly {K : Type} [Field K] (A : AbVar K) (f : End A) : ∃ P, IsCharpoly f P := by
  obtain ⟨P, hPm, hPd, hPe⟩ := GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety K A f
  obtain ⟨l, hl, hlK⟩ := exists_prime_natCast_ne_zero_of_field K
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : Module.Finite ℚ_[l] (Vl l A) := (tl_free_finrank K l hlK A).2.2.2.1
  have hcp := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hlK A f P hPm hPd hPe
  haveI : Module.Finite ℤ (End A) := (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A).1
  obtain ⟨Q, hQm, hQ⟩ := (Algebra.IsIntegral.isIntegral f : IsIntegral ℤ f)
  have hQV : Polynomial.aeval (vmap l (A := A) (B := A) f) Q = 0 := by
    have h := congrArg (vendRing l A) hQ
    rw [Polynomial.hom_eval₂, map_zero,
      Subsingleton.elim ((vendRing l A).comp (algebraMap ℤ (End A))) (algebraMap ℤ _)] at h
    rw [Polynomial.aeval_def, ← vendRing_apply]
    exact h
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator ℚ_[l] (Vl l A) (vmap l (A := A) (B := A) f) P Q hQm hQV hcp
  have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  refine ⟨P₀, ?_, ?_, ?_⟩
  · have h := hPm
    rw [← hP₀] at h
    rw [Polynomial.Monic, Polynomial.leadingCoeff_map_of_injective hinj] at h
    exact hinj (by simpa using h)
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hP₀, hPd]
  · intro n
    have h := hPe n
    rw [← hP₀, Polynomial.eval_map, show (n : ℚ) = algebraMap ℤ ℚ n by simp,
      Polynomial.eval₂_hom] at h
    rw [eq_intCast] at h
    exact_mod_cast h

theorem isCharpoly_charpoly_unique (K : Type) [Field K] (A : AbVar K) (f : End A) :
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  have hex := exists_isCharpoly A f
  have hc : IsCharpoly f (charpoly f) := by
    classical
    rw [charpoly, dif_pos hex]
    exact hex.choose_spec
  refine ⟨hc, fun P hP => Polynomial.funext fun n => ?_⟩
  rw [hP.2.2 n, hc.2.2 n]

theorem charpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A),
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f :=
  fun K _ A f => isCharpoly_charpoly_unique K A f

end GlobalTheory.AV.AbVar
