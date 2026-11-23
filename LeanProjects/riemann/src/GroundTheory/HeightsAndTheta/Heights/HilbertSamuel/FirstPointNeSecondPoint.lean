import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FderivFderivLogRho
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace P1

abbrev Fld : Type := FractionRing (Polynomial ℤ)

instance : CharZero Fld :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (Polynomial ℤ) Fld)

instance (priority := 10000) fldAlgInt : Algebra ℤ Fld := Ring.toIntAlgebra Fld

abbrev J2 : Type := Ix (Fin 2)

def p0 : J2 := ⟨(), 0⟩

def p1 : J2 := ⟨(), 1⟩

theorem twoPoint_cases (q : J2) : q = p0 ∨ q = p1 := by
  obtain ⟨⟨⟩, i⟩ := q
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem firstPoint_ne_secondPoint : p0 ≠ p1 := by
  decide

theorem sum_twoPoint {M : Type*} [AddCommMonoid M] (g : J2 → M) : ∑ q, g q = g p0 + g p1 := by
  rw [Fintype.sum_sigma]
  simp [Fin.sum_univ_two, p0, p1]

def val (q : J2) : Polynomial ℤ := if q.2 = 0 then 1 else Polynomial.X

def x : J2 → Fld := fun q ↦ algebraMap (Polynomial ℤ) Fld (val q)

def dehom : MvPolynomial J2 ℤ →+* Polynomial ℤ := eval₂Hom (Int.castRingHom _) val

theorem aeval_alt (f : MvPolynomial J2 ℤ) : aeval x f = algebraMap (Polynomial ℤ) Fld (dehom f) := by
  have : (aeval x : MvPolynomial J2 ℤ →ₐ[ℤ] Fld).toRingHom =
      (algebraMap (Polynomial ℤ) Fld).comp dehom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [dehom]
    · intro q; simp [dehom, x]
  exact congrArg (fun φ : MvPolynomial J2 ℤ →+* Fld ↦ φ f) this

def homog (p : Polynomial ℤ) (d : ℕ) : MvPolynomial J2 ℤ :=
  ∑ i ∈ Finset.range (d + 1), monomial (Finsupp.single p1 i + Finsupp.single p0 (d - i)) (p.coeff i)

theorem monomial_eq (i j : ℕ) (c : ℤ) :
    monomial (Finsupp.single p1 i + Finsupp.single p0 j) c = C c * (X p1 ^ i * X p0 ^ j) := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial, one_mul, mul_one]

theorem dehom_monomial (i j : ℕ) (c : ℤ) :
    dehom (monomial (Finsupp.single p1 i + Finsupp.single p0 j) c) = Polynomial.C c * Polynomial.X ^ i := by
  rw [monomial_eq, map_mul, map_mul, map_pow, map_pow]
  simp only [dehom, coe_eval₂Hom, eval₂_C, eval₂_X, val, p0, p1]
  simp

theorem dehom_homog (p : Polynomial ℤ) {d : ℕ} (hp : p.natDegree ≤ d) : dehom (homog p d) = p := by
  rw [homog, map_sum]
  simp_rw [dehom_monomial]
  conv_rhs => rw [p.as_sum_range' (d + 1) (by omega)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial]

theorem isMultiHomog_homog (p : Polynomial ℤ) (d : ℕ) :
    IsMultiHomog (ι := GlobalTheory (Fin 2)) (homog p d) fun _ ↦ d := by
  intro m hm k
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  have hm' : m = Finsupp.single p1 i + Finsupp.single p0 (d - i) := by
    by_contra hne
    rw [support_monomial] at hmi
    split_ifs at hmi with hc
    · simp at hmi
    · exact hne (Finset.mem_singleton.mp hmi)
  subst hm'
  obtain ⟨⟩ := k
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Fin.sum_univ_two]
  simp [Finsupp.single_apply, p0, p1]
  omega

theorem homog_add (p q : Polynomial ℤ) (d : ℕ) : homog (p + q) d = homog p d + homog q d := by
  simp [homog, Polynomial.coeff_add, map_add, Finset.sum_add_distrib]

theorem homog_zero (d : ℕ) : homog 0 d = 0 := by simp [homog]

theorem homog_C_mul_X_pow (c : ℤ) {j d : ℕ} (hj : j ≤ d) :
    homog (Polynomial.C c * Polynomial.X ^ j) d =
      monomial (Finsupp.single p1 j + Finsupp.single p0 (d - j)) c := by
  rw [homog, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Polynomial.coeff_C_mul_X_pow, hij]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem finsupp_twoPoint_eq (m : J2 →₀ ℕ) : m = Finsupp.single p1 (m p1) + Finsupp.single p0 (m p0) := by
  ext q
  rcases twoPoint_cases q with rfl | rfl
  · simp [Finsupp.single_apply, firstPoint_ne_secondPoint.symm]
  · simp [Finsupp.single_apply, firstPoint_ne_secondPoint]

theorem homog_dehom {f : MvPolynomial J2 ℤ} {d : ℕ} (hf : f.IsHomogeneous d) :
    homog (dehom f) d = f := by
  let H : Polynomial ℤ →+ MvPolynomial J2 ℤ :=
    { toFun := fun p ↦ homog p d, map_zero' := homog_zero d, map_add' := fun p q ↦ homog_add p q d }
  have key : ∀ m ∈ f.support, H (dehom (monomial m (f.coeff m))) = monomial m (f.coeff m) := by
    intro m hm
    have hdeg : m p0 + m p1 = d := by
      have := hf (mem_support_iff.mp hm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
      rw [Finsupp.sum_fintype _ _ (by simp), sum_twoPoint] at this
      exact this
    conv_lhs => rw [finsupp_twoPoint_eq m]
    rw [dehom_monomial]
    change homog _ d = _
    rw [homog_C_mul_X_pow _ (by omega), show d - m p1 = m p0 by omega, ← finsupp_twoPoint_eq m]
  conv_lhs => rw [f.as_sum]
  change H (dehom (∑ m ∈ f.support, monomial m (f.coeff m))) = _
  rw [map_sum, map_sum]
  conv_rhs => rw [f.as_sum]
  exact Finset.sum_congr rfl key

theorem coordIdeal_alt : coordIdeal ℤ x = ⊥ := by
  ext f
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hcomp : ∀ d, homogeneousComponent d f = 0 := fun d ↦ by
      have h1 : aeval x (homogeneousComponent d f) = 0 := by
        rw [← coeff_coneMap ℤ x f d]
        rw [coordIdeal, RingHom.mem_ker] at hf
        rw [hf, Polynomial.coeff_zero]
      rw [aeval_alt] at h1
      have h2 : dehom (homogeneousComponent d f) = 0 :=
        IsFractionRing.injective (Polynomial ℤ) Fld (by rw [h1, map_zero])
      rw [← homog_dehom (homogeneousComponent_isHomogeneous d f), h2, homog_zero]
    rw [Submodule.mem_bot, ← sum_homogeneousComponent f]
    simp [hcomp]
  · rw [Submodule.mem_bot] at hf
    rw [hf]
    exact Submodule.zero_mem _

theorem isArithVar_alt : IsArithVar (ι := GlobalTheory (Fin 2)) (coordIdeal ℤ x) (1 + 1) := by
  rw [coordIdeal_alt]
  exact Inter.isArithVar_projLine

theorem linearIndependent_alt : LinearIndependent ℤ x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  rw [sum_twoPoint] at hg
  have h : algebraMap (Polynomial ℤ) Fld (Polynomial.C (g p0) + Polynomial.C (g p1) * Polynomial.X) =
      0 := by
    rw [← hg]
    simp [x, val, p0, p1, zsmul_eq_mul]
  have hp : Polynomial.C (g p0) + Polynomial.C (g p1) * Polynomial.X = 0 :=
    IsFractionRing.injective (Polynomial ℤ) Fld (by rw [h, map_zero])
  have h0 := congrArg (Polynomial.coeff · 0) hp
  have h1 := congrArg (Polynomial.coeff · 1) hp
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X] at h0 h1
  simp at h0 h1
  rcases twoPoint_cases q with rfl | rfl
  · exact h0
  · exact h1

theorem birational_alt : Birational (ι := GlobalTheory (Fin 2)) x := by
  intro s
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial ℤ) s
  set D := max p.natDegree q.natDegree
  have hq0 : algebraMap (Polynomial ℤ) Fld q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  refine ⟨fun _ ↦ D, homog p D, homog q D, isMultiHomog_homog p D, isMultiHomog_homog q D, ?_, ?_⟩
  · rw [aeval_alt, dehom_homog q (le_max_right _ _)]
    exact hq0
  · rw [aeval_alt, aeval_alt, dehom_homog p (le_max_left _ _), dehom_homog q (le_max_right _ _),
      div_mul_cancel₀ _ hq0]

abbrev fs : ConeMetric ℂ J2 := fsMetric J2

theorem rho_fs (z : J2 → ℂ) : fs.ρ z = Real.sqrt (FSLevi.nsq z) := by
  have h := FSLevi.log_rho_eq z
  simp [fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply, FSLevi.imaginaryPart_apply,
    FSLevi.norm_sq_eq]

theorem isSmoothHerm_fs {κ : Type} [Fintype κ] : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix κ))) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FSLevi.nsq (J := Ix κ)) := by
    unfold FSLevi.nsq
    exact ContDiff.sum fun p _ ↦ ((FSLevi.reP p).contDiff.pow 2).add ((FSLevi.imaginary p).contDiff.pow 2)
  have he : (HermLine.ofCone (fsMetric (Ix κ))).h = fun z ↦ Real.sqrt (FSLevi.nsq z) := by
    funext z
    simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply,
      FSLevi.imaginaryPart_apply, FSLevi.norm_sq_eq]
  unfold IsSmoothHerm
  rw [he]
  refine hN.contDiffOn.sqrt fun z hz ↦ (FSLevi.nsq_pos ?_).ne'
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 ↦ hi (congrFun h0 _)

theorem isConjInvariantH_fs {κ : Type} [Fintype κ] :
    IsConjInvariantH (HermLine.ofCone (fsMetric (Ix κ))) := by
  intro z
  simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]

theorem isSemipositiveRel_fs {κ : Type} [Fintype κ] (P₀ P : Ideal (MRing (GlobalTheory κ))) :
    IsSemipositiveRel P₀ P (HermLine.ofCone (fsMetric (Ix κ))) := by
  refine ⟨isSmoothHerm_fs, fun z hz w _ ↦ ?_⟩
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := hz.1 ()
    exact fun h0 ↦ hi (congrFun h0 _)
  exact FSLevi.leviForm_nonneg hz0 w

theorem isHSDatum : IsHSDatum 1 x fs ⊥ :=
  ⟨le_rfl, isArithVar_alt, linearIndependent_alt, bot_le,
    isSemipositiveRel_fs (κ := Fin 2) ⊥ (coordIdeal ℤ x), isConjInvariantH_fs (κ := Fin 2)⟩

end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
