import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.DegreeTautologicalLineProjectiveLine
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPowerSumOneZeroStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top.HhTestProof

open scoped ComplexOrder MatrixOrder in

theorem det_one_add_bound {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℂ) (hZ : ∀ i k, ‖Z i k‖ = 1) :
    0 < (1 + Z * Z.conjTranspose).det.re ∧ (1 + Z * Z.conjTranspose).det.re ≤ (1 + (b : ℝ)) ^ a := by
  have hA : (1 + Z * Z.conjTranspose).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose Z)
  refine ⟨(Complex.pos_iff.mp hA.det_pos).1, ?_⟩
  refine (ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard hA).trans (le_of_eq ?_)
  have hd : ∀ i : Fin a, (((1 : Matrix (Fin a) (Fin a) ℂ) + Z * Z.conjTranspose) i i).re = 1 + (b : ℝ) := by
    intro i
    have h1 : (Z * Z.conjTranspose) i i = ∑ k, Z i k * star (Z i k) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have h2 : ∀ k, (Z i k * star (Z i k)).re = 1 := by
      intro k
      have := Complex.mul_conj (Z i k)
      rw [Complex.star_def, this, Complex.normSq_eq_norm_sq, hZ]
      simp
    rw [Matrix.add_apply, Matrix.one_apply_eq, Complex.add_re, Complex.one_re, h1, Complex.re_sum,
      Finset.sum_congr rfl fun k _ => h2 k]
    simp
  rw [Finset.prod_congr rfl fun i _ => hd i]
  simp

theorem half_log_det_le {j m N : ℕ} (hN : j + m = N) (Z : Matrix (Fin m) (Fin j) ℂ) (hZ : ∀ i k, ‖Z i k‖ = 1) :
    1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ ((min j m : ℕ) : ℝ) / 2 * Real.log ((N : ℝ) + 1) := by
  have hNr : (j : ℝ) + m = N := by exact_mod_cast hN
  have key : ∀ (c d : ℕ), c + d = N → ∀ x : ℝ, 0 < x → x ≤ (1 + (d : ℝ)) ^ c →
      1 / 2 * Real.log x ≤ (c : ℝ) / 2 * Real.log ((N : ℝ) + 1) := by
    intro c d hcd x hx hle
    have hcdr : (c : ℝ) + d = N := by exact_mod_cast hcd
    have h1 : Real.log x ≤ (c : ℝ) * Real.log (1 + (d : ℝ)) := by
      have := Real.log_le_log hx hle
      rwa [Real.log_pow] at this
    have h2 : Real.log (1 + (d : ℝ)) ≤ Real.log ((N : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
      linarith
    have h3 : (c : ℝ) * Real.log (1 + (d : ℝ)) ≤ (c : ℝ) * Real.log ((N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
    linarith
  rcases le_total m j with h | h
  · rw [min_eq_right h]
    obtain ⟨h0, h1⟩ := det_one_add_bound Z hZ
    exact key m j (by omega) _ h0 h1
  · rw [min_eq_left h]
    have hcomm : (1 + Z * Z.conjTranspose).det = (1 + Z.conjTranspose * Z).det :=
      Matrix.det_one_add_mul_comm _ _
    have hZ' : ∀ i k, ‖Z.conjTranspose i k‖ = 1 := by
      intro i k
      simp [Matrix.conjTranspose_apply, hZ]
    obtain ⟨h0, h1⟩ := det_one_add_bound Z.conjTranspose hZ'
    rw [Matrix.conjTranspose_conjTranspose] at h0 h1
    rw [hcomm]
    exact key j m (by omega) _ h0 h1

section Poly

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def negX : RP Ψ N →ₐ[ℝ] RP Ψ N := aeval fun x => -X x

theorem negX_monomial (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    negX (monomial m c : RP Ψ N) = monomial m ((-1) ^ m.degree * c) := by
  have h1 : (m.prod fun i k => (-X i : RP Ψ N) ^ k) =
      C ((-1) ^ m.degree) * m.prod fun i k => (X i : RP Ψ N) ^ k := by
    rw [Finsupp.prod, Finsupp.prod]
    have : ∀ i ∈ m.support, (-X i : RP Ψ N) ^ m i = C ((-1) ^ m i) * X i ^ m i := by
      intro i _
      rw [neg_pow, map_pow, map_neg, map_one]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_pow_eq_pow_sum]
    rfl
  rw [negX, aeval_monomial, h1, monomial_eq (a := (-1) ^ m.degree * c), map_mul, algebraMap_eq]
  ring

theorem coeff_negX (m : Ψ × Fin N →₀ ℕ) (F : RP Ψ N) :
    coeff m (negX F) = (-1) ^ m.degree * coeff m F := by
  induction F using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [negX_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]; ring

end Poly

section Funs

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def hR (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (II : IntersectionSystem) : RP Ψ N →ₗ[ℝ] ℝ :=
  (basisMonomials (Ψ × Fin N) ℝ).constr ℝ fun m => GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m

theorem hR_monomial (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    hR Ψ N II (monomial m c) = c * GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m := by
  have h : (monomial m c : RP Ψ N) = c • basisMonomials (Ψ × Fin N) ℝ m := by
    simp [smul_monomial]
  rw [h, map_smul, hR, Module.Basis.constr_basis, smul_eq_mul]

theorem hhFl_monomial (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    hhFl Ψ N II (monomial m c) = c * ((-1) ^ m.degree * GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m) := by
  have h : (monomial m c : RP Ψ N) = c • basisMonomials (Ψ × Fin N) ℝ m := by
    simp [smul_monomial]
  rw [h, map_smul, hhFl, Module.Basis.constr_basis, smul_eq_mul]

theorem hhFl_eq (II : IntersectionSystem) (F : RP Ψ N) : hhFl Ψ N II F = hR Ψ N II (negX F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u c => rw [negX_monomial, hhFl_monomial, hR_monomial]; ring
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

theorem hFl_eq (II : IntersectionSystem) (G : GroundTheory.Heights₂.Heights.LowerBoundFree.RootPoly Ψ N) :
    GroundTheory.Heights₂.Heights.LowerBoundFree.hFl Ψ N II G = hR Ψ N II (map (algebraMap ℚ ℝ) G) := by
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, GroundTheory.Heights₂.Heights.LowerBoundFree.hFl]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, hR_monomial]
  rfl

def flR (F : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * F.coeff (permExp σ)

theorem degFl_eq_flR (F : RP Ψ N) : degFl F = flR (negX F) := by
  rw [degFl, flR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hd : (permExp σ).degree = dimFl Ψ N := Formalism.DegreeFormula.PPowSum.degree_permExp σ
  rw [coeff_negX, hd]
  ring

theorem flagInt_eq (G : GroundTheory.Heights₂.Heights.LowerBoundFree.RootPoly Ψ N) :
    ((GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt Ψ N G : ℚ) : ℝ) = flR (map (algebraMap ℚ ℝ) G) := by
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt, GroundTheory.Heights₂.Heights.LowerBoundFree.antisym, coeff_sum,
    flR, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hinj : Function.Injective (GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ) := by
    rintro ⟨a, i⟩ ⟨b, k⟩ h
    simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp [(σ a).injective h]
  have hm : GroundTheory.Heights₂.Heights.LowerBoundFree.rhoMono Ψ N =
      (permExp σ).mapDomain (GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ) := by
    ext ⟨τ, i⟩
    have : (τ, i) = GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ (τ, (σ τ).symm i) := by
      simp [GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct]
    rw [this, Finsupp.mapDomain_apply hinj]
    simp [GroundTheory.Heights₂.Heights.LowerBoundFree.rhoMono, permExp, GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct]
  rw [coeff_smul, hm, coeff_rename_mapDomain _ hinj, smul_eq_mul, Rat.cast_mul, coeff_map]
  congr 1
  simp [GroundTheory.Heights₂.Heights.LowerBoundFree.weylSign]

end Funs

section Test

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def muR (j : ℕ) : RP Ψ N := map (algebraMap ℚ ℝ) (GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly Ψ N j)

def vR (j : ℕ) : RP Ψ N := map (algebraMap ℚ ℝ) (GroundTheory.Heights₂.Heights.LowerBoundFree.vandBlocks Ψ N j)

theorem muR_eq (j : ℕ) : (muR j : RP Ψ N) = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) := by
  rw [muR, GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly, map_sum, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem negX_muR (j : ℕ) : negX (muR j : RP Ψ N) = -muR j := by
  rw [muR_eq, negX, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_X]

theorem negX_fibClass (j : ℕ) : negX (fibClass j : RP Ψ N) = vR j := by
  rw [fibClass, vR, GroundTheory.Heights₂.Heights.LowerBoundFree.vandBlocks, negX, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun ab _ => ?_
  simp only [map_sub, aeval_X, map_X]
  ring

def sAll : RP Ψ N := ∑ τ, pk τ 1

theorem muSmall_of_le {j : ℕ} (h : N - j ≤ j) : (muSmall j : RP Ψ N) = muR j := by
  rw [muSmall, if_pos h, muR_eq]

theorem muR_sub_muSmall {j : ℕ} (h : ¬ N - j ≤ j) : (muR j : RP Ψ N) - muSmall j = sAll := by
  rw [muSmall, if_neg h, muR_eq, sAll, sub_neg_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [pk, pkLow, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem degFl_sAll_mul (Q : RP Ψ N) : degFl ((sAll : RP Ψ N) * Q) = 0 := by
  rw [sAll, Finset.sum_mul]
  refine Finset.sum_induction _ (fun x : RP Ψ N => degFl x = 0) ?_ ?_ ?_
  · intro a b ha hb
    rw [Model.degFl_add, ha, hb, add_zero]
  · simp [degFl]
  · intro τ _
    exact Model.degFl_pk_mul τ 1 le_rfl Q

theorem muR_homog (j : ℕ) : (muR j : RP Ψ N).IsHomogeneous 1 := by
  rw [muR_eq]
  exact IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X _ _

theorem muSmall_homog (j : ℕ) : (muSmall j : RP Ψ N).IsHomogeneous 1 := by
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]; exact muR_homog j
  · rw [muSmall, if_neg h]
    refine IsHomogeneous.neg ?_
    refine IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => ?_
    rw [pow_one]
    exact isHomogeneous_X _ _

theorem fibClass_homog (j : ℕ) : ∃ d, (fibClass j : RP Ψ N).IsHomogeneous d := by
  refine ⟨_, IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ (fun _ => 1) fun ab _ => ?_⟩
  exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

end Test

section Main

open GroundTheory.Heights₂.Heights.LowerBoundFree (FA Jint fib dimN)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem dimN_eq (j : ℕ) : dimN Ψ N j = dimX Ψ N j := by
  rw [dimN, dimX, Nat.mul_assoc]

theorem negX_pow_mul (k j : ℕ) :
    negX ((muR j : RP Ψ N) ^ k * fibClass j) = ((-1 : ℝ) ^ k) • ((muR j : RP Ψ N) ^ k * vR j) := by
  rw [map_mul, map_pow, negX_muR, negX_fibClass, neg_pow, smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

theorem map_FA (j : ℕ) (cf : ℚ) :
    map (algebraMap ℚ ℝ) (FA Ψ N j cf) = (cf : ℝ) • ((muR j : RP Ψ N) ^ (dimN Ψ N j + 1) * vR j) := by
  rw [FA, fib, map_mul, map_pow, map_mul, map_C, smul_eq_C_mul]
  change _ * (C ((cf : ℝ)) * _) = _
  rw [muR, vR]
  ring

theorem map_J (j : ℕ) (cf : ℚ) :
    map (algebraMap ℚ ℝ) ((GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly Ψ N j) ^ (dimN Ψ N j) *
      fib Ψ N j cf) = (cf : ℝ) • ((muR j : RP Ψ N) ^ (dimN Ψ N j) * vR j) := by
  rw [fib, map_mul, map_pow, map_mul, map_C, smul_eq_C_mul]
  change _ * (C ((cf : ℝ)) * _) = _
  rw [muR, vR]
  ring

theorem hhFl_muR (II : IntersectionSystem) (j : ℕ) :
    hhFl Ψ N II ((muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j) =
      -GroundTheory.Heights₂.Heights.LowerBoundFree.hFl Ψ N II (FA Ψ N j ((-1) ^ dimX Ψ N j)) := by
  rw [hhFl_eq, negX_pow_mul, hFl_eq, map_FA, dimN_eq, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem degFl_muR (j : ℕ) :
    degFl ((muR j : RP Ψ N) ^ dimX Ψ N j * fibClass j) = ((Jint Ψ N j ((-1) ^ dimX Ψ N j) : ℚ) : ℝ) := by
  rw [degFl_eq_flR, negX_pow_mul, Jint, flagInt_eq, map_J, dimN_eq]
  push_cast
  rfl

theorem testDeg_eq (j : ℕ) :
    testDeg Ψ N j = ((Jint Ψ N j ((-1) ^ dimX Ψ N j) : ℚ) : ℝ) := by
  rw [← degFl_muR, testDeg]
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]
  · have e := geom_sum₂_mul (muR j : RP Ψ N) (muSmall j) (dimX Ψ N j)
    rw [muR_sub_muSmall h] at e
    have e2 : (muR j : RP Ψ N) ^ dimX Ψ N j * fibClass j = muSmall j ^ dimX Ψ N j * fibClass j +
        sAll * ((∑ i ∈ Finset.range (dimX Ψ N j), (muR j : RP Ψ N) ^ i * muSmall j ^ (dimX Ψ N j - 1 - i)) *
          fibClass j) := by
      rw [← mul_assoc, mul_comm sAll, e]
      ring
    rw [e2, Model.degFl_add, degFl_sAll_mul, add_zero]

theorem degree_count {j d : ℕ} (hn : dimX Ψ N j ≠ 0)
    (hT : (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1)) (hdeg : 0 < testDeg Ψ N j)
    (hf : (fibClass j : RP Ψ N).IsHomogeneous d) : dimX Ψ N j + d = dimFl Ψ N := by
  have h0 : (muSmall j : RP Ψ N) ^ dimX Ψ N j * fibClass j ≠ 0 := by
    intro h
    rw [testDeg, h] at hdeg
    simp [degFl] at hdeg
  have hM : (muSmall j : RP Ψ N) ≠ 0 := by
    intro h
    rw [h, zero_pow hn, zero_mul] at h0
    exact h0 rfl
  have hT0 : (testPoly j : RP Ψ N) ≠ 0 := by
    rw [testPoly, pow_succ', mul_assoc]
    exact mul_ne_zero hM h0
  have h2 : (testPoly j : RP Ψ N).IsHomogeneous (1 * (dimX Ψ N j + 1) + d) :=
    ((muSmall_homog j).pow _).mul hf
  have := h2.inj_right hT hT0
  omega

theorem hhFl_test (II : IntersectionSystem) {j d : ℕ}
    (hkill : ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0)
    (hf : (fibClass j : RP Ψ N).IsHomogeneous d) (hd : dimX Ψ N j + d = dimFl Ψ N) :
    hhFl Ψ N II (testPoly j) = hhFl Ψ N II ((muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j) := by
  rw [testPoly]
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]
  · have e := geom_sum₂_mul (muR j : RP Ψ N) (muSmall j) (dimX Ψ N j + 1)
    rw [muR_sub_muSmall h] at e
    set Q : RP Ψ N := (∑ i ∈ Finset.range (dimX Ψ N j + 1),
      (muR j : RP Ψ N) ^ i * muSmall j ^ (dimX Ψ N j + 1 - 1 - i)) * fibClass j with hQ
    have e2 : (muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j =
        muSmall j ^ (dimX Ψ N j + 1) * fibClass j + sAll * Q := by
      rw [hQ, ← mul_assoc, mul_comm sAll, e]
      ring
    have hQh : Q.IsHomogeneous (dimFl Ψ N) := by
      rw [← hd, hQ]
      refine IsHomogeneous.mul ?_ hf
      refine IsHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have := ((muR_homog (Ψ := Ψ) (N := N) j).pow i).mul ((muSmall_homog (Ψ := Ψ) (N := N) j).pow (dimX Ψ N j + 1 - 1 - i))
      have e3 : 1 * i + 1 * (dimX Ψ N j + 1 - 1 - i) = dimX Ψ N j := by omega
      rwa [e3] at this
    rw [e2, map_add, sAll, Finset.sum_mul, map_sum, Finset.sum_eq_zero fun τ _ => hkill τ Q hQh, add_zero]

end Main

theorem hhTestBound_hhFl : GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → PB.Inputs →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
      [Nonempty Ψ] (j : ℕ), 1 ≤ j → j < N → HhTestBound j (hhFl Ψ N II) := by
  intro hZ2 _ II hII Ψ _ _ N _ j hj hjN
  have hN : 2 ≤ N := by omega
  obtain ⟨hT, hdeg, -, -⟩ := GlobalTheory.T.test_polynomial_shift_total Ψ N j hj hjN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    have := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
    rwa [GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right] at this
  have hkill : ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0 :=
    fun τ Q hQ => GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ
  have hn : dimX Ψ N j ≠ 0 := by
    have h1 : 0 < Fintype.card Ψ := Fintype.card_pos
    have h2 : 0 < N - j := by omega
    exact (Nat.mul_pos h1 (Nat.mul_pos (by omega) h2)).ne'
  obtain ⟨d, hf⟩ := fibClass_homog (Ψ := Ψ) (N := N) j
  have hd := degree_count hn hT hdeg hf
  have hJ := testDeg_eq (Ψ := Ψ) (N := N) j
  have hJ0 : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.Jint Ψ N j ((-1) ^ dimX Ψ N j) := by
    rw [hJ] at hdeg
    exact_mod_cast hdeg
  have hb := hZ2 II Ψ N j ((-1) ^ dimX Ψ N j) (((min j (N - j) : ℕ) : ℝ) / 2 * Real.log ((N : ℝ) + 1))
    hII.1 hN hj (by omega) hJ0
    (fun Z hZ => half_log_det_le (by omega) Z hZ)
  rw [HhTestBound, hhFl_test II hkill hf hd, hhFl_muR, hJ]
  rw [dimN_eq] at hb
  refine hb.trans (le_of_eq ?_)
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Top.HhTestProof
