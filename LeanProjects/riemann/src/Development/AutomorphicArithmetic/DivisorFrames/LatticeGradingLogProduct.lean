import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticePrimeToPBasis
import Development.AutomorphicArithmetic.DivisorFrames.IdealNormLogHeight
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead

namespace UpperTheory.NormDeterminantRelation

private theorem det_rel {K : Type} [Field K] [NumberField K] {g : ℕ} (x y : Fin g → Fin g → K) (s : ℕ)
    (h : ∀ k, (s : K) • y k ∈ Submodule.span (𝓞 K) (Set.range x)) :
    ∃ r : 𝓞 K, (s : K) ^ g * (Matrix.of fun i k => y k i).det = r • (Matrix.of fun i k => x k i).det := by
  choose m hm using fun k => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (h k)
  let A : Matrix (Fin g) (Fin g) (𝓞 K) := Matrix.of fun l k => m k l
  have hmat : (s : K) • (Matrix.of fun i k => y k i) =
      (Matrix.of fun i k => x k i) * A.map (algebraMap (𝓞 K) K) := by
    ext i k
    have := congrFun (hm k) i
    rw [Finset.sum_apply] at this
    rw [Matrix.smul_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [Pi.smul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, Matrix.of_apply, Matrix.map_apply, Algebra.smul_def, mul_comm]
    rfl
  refine ⟨A.det, ?_⟩
  have hd := congrArg Matrix.det hmat
  rw [Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hd
  rw [hd, Algebra.smul_def, mul_comm]
  congr 1
  exact (RingHom.map_det (algebraMap (𝓞 K) K) A).symm

private theorem norm_int_le {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (j : K →+* ℂ_[p])
    (r : 𝓞 K) : ‖j (r : K)‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨q, hq, hqr₀⟩ := RingOfIntegers.isIntegral_coe r
  have hqr : Polynomial.eval₂ (Int.castRingHom ℂ_[p]) (j (r : K)) q = 0 := by
    have h0 := congrArg j hqr₀
    rw [Polynomial.hom_eval₂, map_zero] at h0
    rw [← h0]
    congr 1
    exact RingHom.ext_int _ _
  set x : ℂ_[p] := j (r : K) with hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hqr
  have h1 : x ^ q.natDegree = - ∑ i ∈ Finset.range q.natDegree, Int.castRingHom ℂ_[p] (q.coeff i) * x ^ i := by
    linear_combination hqr
  have h2 : ∀ s : Finset ℕ, (∀ i ∈ s, i < q.natDegree) →
      ‖∑ i ∈ s, Int.castRingHom ℂ_[p] (q.coeff i) * x ^ i‖ < ‖x‖ ^ q.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp; positivity
    | insert i s hi ih =>
      intro hs
      rw [Finset.sum_insert hi]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (max_lt ?_ (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))
      rw [norm_mul, norm_pow]
      have h3 : ‖((q.coeff i : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
      have h4 : ‖x‖ ^ i < ‖x‖ ^ q.natDegree := pow_lt_pow_right₀ h (hs i (Finset.mem_insert_self _ _))
      have h5 : 0 ≤ ‖x‖ ^ i := by positivity
      simp only [eq_intCast]
      nlinarith
  have h6 := h2 _ (fun i hi => Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h6
  exact lt_irrefl _ h6

private theorem norm_nat_eq (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : ‖(s : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hs
  have h2 := PadicComplex.norm_extends' p (s : ℚ_[p])
  rw [h1] at h2
  simpa using h2

end UpperTheory.NormDeterminantRelation

open UpperTheory.NormDeterminantRelation in
theorem UpperTheory.lattice_grading_log_product :
    ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (L : Submodule (𝓞 K) (Fin g → K)), Full L → ∃ (c : K) (t : ℝ), c ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (j : K →+* ℂ_[p]), ∑ k, lnGrP p j L k = -(t * Real.log ‖j c‖) := by
  intro K _ _ g L hL
  classical
  let S : Set K := {d | ∃ x : Fin g → Fin g → K, (∀ i, x i ∈ L) ∧ d = (Matrix.of fun i k => x k i).det}
  let 𝔞 : Submodule (𝓞 K) K := Submodule.span (𝓞 K) S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, s₀, hx₀, hi₀, hs₀, hsp₀⟩ := GlobalTheory.FullLatLocBasis.exists_basis_primeTo_p K g 2 L hL
  have hs0 : (s₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hs₀ (dvd_zero 2))
  have hdet0 : (Matrix.of fun i k => x₀ k i).det ≠ 0 := by
    have hu : IsUnit (Matrix.of fun i k => x₀ k i) := Matrix.linearIndependent_cols_iff_isUnit.mp hi₀
    exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hu).ne_zero
  have hfg : 𝔞.FG := by
    have hle : 𝔞 ≤ Submodule.span (𝓞 K) {((s₀ : K) ^ g)⁻¹ * (Matrix.of fun i k => x₀ k i).det} := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨r, hr⟩ := det_rel x₀ y s₀ fun k => hsp₀ _ (hy k)
      refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
      rw [← mul_smul_comm, ← hr, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_mul]
    exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle
  obtain ⟨n, c, hn, hc, hw, -⟩ := UpperTheory.ideal_norm_log_height K 𝔞 _ hfg (Submodule.subset_span ⟨x₀, hx₀, rfl⟩) hdet0
  refine ⟨c, 1 / n, hc, fun p _ j => ?_⟩
  obtain ⟨x, s, hx, hi, hs, hsp⟩ := GlobalTheory.FullLatLocBasis.exists_basis_primeTo_p K g p L hL
  rw [GlobalTheory.T.lattice_padic_grading_det K g p j L x s hx hi hs hsp]
  let w : AbsoluteValue K ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective
  have hwa : ∀ b, w b = ‖j b‖ := fun b => rfl
  have hna : IsNonarchimedean w := fun a b => by
    rw [hwa, hwa, hwa, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hsm : ∀ (r : 𝓞 K) (b : K), ‖j (r • b)‖ ≤ ‖j b‖ := fun r b => by
    rw [Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_int_le p j r)
  have hub : ∀ b ∈ 𝔞, ‖j b‖ ≤ ‖j (Matrix.of fun i k => x k i).det‖ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, hy, rfl⟩ := hb
      obtain ⟨r, hr⟩ := det_rel x y s fun k => hsp _ (hy k)
      have h1 := hsm r (Matrix.of fun i k => x k i).det
      rw [← hr, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_nat_eq p s hs, one_pow, one_mul] at h1
      exact h1
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul r a _ ha => exact (hsm r a).trans ha
  have hsup : sSup ((fun b => w b) '' (𝔞 : Set K)) = ‖j (Matrix.of fun i k => x k i).det‖ := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hub b hb
  have h := hw w hna
  rw [hsup, hwa] at h
  rw [← h, Real.log_pow]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
