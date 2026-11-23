import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Lin

variable {J : Type} [Fintype J] [DecidableEq J]

theorem isInvMat_mul {A : Matrix J J ℚ} (hA : IsInvMat A) :
    ∃ B : Matrix J J ℚ, A * B = 1 ∧ B * A = 1 := by
  obtain ⟨B, hB⟩ := hA
  refine ⟨B, ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).1
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).2

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem matAct_eq_mulVec (A : Matrix J J ℚ) (v : J → Ω) :
    matAct A v = (A.map (Rat.castHom Ω)).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

theorem matAct_matAct {A B : Matrix J J ℚ} (h : B * A = 1) (v : J → Ω) :
    matAct B (matAct A v) = v := by
  rw [matAct_eq_mulVec, matAct_eq_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem matActC_eq (A : Matrix J J ℚ) (z : J → ℂ) : matActC A z = matAct A z := rfl

theorem matAct_smul (A : Matrix J J ℚ) (c : Ω) (v : J → Ω) :
    matAct A (c • v) = c • matAct A v := by
  funext i
  simp only [matAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matAct_zero (A : Matrix J J ℚ) : matAct A (0 : J → Ω) = 0 := by
  funext i
  simp [matAct]

theorem matAct_eq_zero_iff {A B : Matrix J J ℚ} (h : B * A = 1) (v : J → Ω) :
    matAct A v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    rw [← matAct_matAct h v, hv, matAct_zero]
  · rintro rfl
    exact matAct_zero A

def linSub (A : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  bind₁ fun i => ∑ j, C (A i j) * X j

theorem aeval_linSub (A : Matrix J J ℚ) (v : J → Ω) (g : MvPolynomial J ℚ) :
    aeval v (linSub A g) = aeval (matAct A v) g := by
  simp only [linSub, aeval_bind₁]
  congr 2
  funext i
  simp [matAct, eq_ratCast]

theorem isHomogeneous_linSub (A : Matrix J J ℚ) {g : MvPolynomial J ℚ} {n : ℕ}
    (hg : g.IsHomogeneous n) : (linSub A g).IsHomogeneous n := by
  have h := hg.eval₂ (algebraMap ℚ (MvPolynomial J ℚ)) (fun i => ∑ j, C (A i j) * X j)
    (fun r => by rw [MvPolynomial.algebraMap_eq]; exact isHomogeneous_C _ _)
    (fun i => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

end Lin

section Pts

variable {J : Type} [Fintype J] {Ω : Type*} [Field Ω] [CharZero Ω]

theorem aeval_int_eq (z : J → ℂ) (f : MvPolynomial J ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem aeval_qmap {S : Type*} [CommRing S] [Algebra ℚ S] (z : J → S) (f : MvPolynomial J ℤ) :
    aeval z (qmap f) = aeval z f := by
  show aeval z (map (Int.castRingHom ℚ) f) = _
  rw [aeval_def, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem mem_pts_iff (v : J → Ω) (z : J → ℂ) :
    z ∈ pts (coordIdeal ℤ v) ↔ z ≠ 0 ∧ ∀ (n : ℕ) (g : MvPolynomial J ℚ), g.IsHomogeneous n →
      aeval v g = 0 → aeval z g = 0 := by
  classical
  simp only [pts, conePts, Set.mem_setOf_eq, coordIdeal, RingHom.mem_ker, aeval_int_eq]
  refine and_congr_right fun _ => ⟨fun H n g hg hv => ?_, fun H f hf => ?_⟩
  · obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
      (g.support.image fun m => g.coeff m)
    have hr' : ∀ m, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * g.coeff m := by
      intro m
      by_cases hm : m ∈ g.support
      · obtain ⟨r, hr⟩ := hb _ (Finset.mem_image_of_mem _ hm)
        exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
      · rw [mem_support_iff, not_not] at hm
        exact ⟨0, by simp [hm]⟩
    choose r hr using hr'
    obtain ⟨f, hfdef⟩ : ∃ f : MvPolynomial J ℤ, f = ∑ m ∈ g.support, monomial m (r m) := ⟨_, rfl⟩
    have hfg : qmap f = C ((b : ℤ) : ℚ) * g := by
      ext m
      rw [coeff_C_mul, ← hr m]
      simp only [qmap, coeff_map, hfdef, coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
      split_ifs with hm
      · simp
      · rw [mem_support_iff, not_not] at hm
        rw [map_zero, hr m, hm, mul_zero]
    have hfh : f.IsHomogeneous n := by
      intro d hd
      apply hg
      intro h0
      apply hd
      have h1 := congrArg (coeff d) hfg
      rw [coeff_C_mul, h0, mul_zero] at h1
      simp only [qmap, coeff_map] at h1
      simpa using h1
    have hvf : aeval v f = 0 := by
      rw [← aeval_qmap, hfg, map_mul, hv, mul_zero]
    have hz := H f (by rw [coneMap_of_isHomogeneous (x := v) (hf := hfh), hvf, map_zero, zero_mul])
    rw [← aeval_qmap, hfg, map_mul, aeval_C] at hz
    have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by simpa using h) hb0
    · exact h
  · have hk : ∀ k, aeval z (homogeneousComponent k f) = 0 := by
      intro k
      have h1 : aeval v (homogeneousComponent k f) = 0 := by
        rw [← coeff_coneMap, hf, Polynomial.coeff_zero]
      have h2 := H k (qmap (homogeneousComponent k f)) ((homogeneousComponent_isHomogeneous k f).map _)
        (by rw [aeval_qmap, h1])
      rwa [aeval_qmap] at h2
    rw [← sum_homogeneousComponent (φ := f), map_sum]
    exact Finset.sum_eq_zero fun k _ => hk k

theorem pts_matAct_gen (x : J → Ω) (A : Matrix J J ℚ) (hA : IsInvMat A) (z : J → ℂ) :
    matActC A z ∈ pts (coordIdeal ℤ (matAct A x)) ↔ z ∈ pts (coordIdeal ℤ x) := by
  classical
  obtain ⟨B, -, hBA⟩ := isInvMat_mul hA
  have hne : matAct A z ≠ 0 ↔ z ≠ 0 := not_congr (matAct_eq_zero_iff hBA z)
  rw [mem_pts_iff, mem_pts_iff, matActC_eq, hne]
  refine and_congr_right fun _ => ⟨fun H n g hg hx => ?_, fun H n g hg hx => ?_⟩
  · have h1 := H n (linSub B g) (isHomogeneous_linSub B hg)
      (by rw [aeval_linSub, matAct_matAct hBA, hx])
    rwa [aeval_linSub, matAct_matAct hBA] at h1
  · rw [← aeval_linSub] at hx ⊢
    exact H n _ (isHomogeneous_linSub A hg) hx

end Pts

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
