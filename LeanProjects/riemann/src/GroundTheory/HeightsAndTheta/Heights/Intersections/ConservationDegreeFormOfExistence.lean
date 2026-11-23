import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace Conservation

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> simp
  · simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem C_not_mem {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by
  intro h
  have : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr h
  rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP, Ideal.mem_bot] at this
  exact ha this

omit [Fintype K] in

theorem isMultiHomog_C (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem comap_eq_of_mem {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
  have hWp : W.IsPrime := hW.1.1.1
  have hpW : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_comap.mpr (hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.IsPrime.comap C).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hpW)).symm

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem not_horizontal {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by
  intro h
  have := comap_eq_of_mem hp hW
  rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from h, eq_comm, Ideal.span_singleton_eq_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charOf_eq {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    charOf W = p := by
  have h := comap_eq_of_mem hp hW
  unfold charOf
  have hg : Ideal.span {Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := by
    rw [← h]; exact Submodule.IsPrincipal.span_singleton_generator _
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at hg
  simpa using hg

theorem vertR_C_prime (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Set.Finite.mem_toFinset] at hV
  rw [if_neg (not_horizontal hp hV), charOf_eq hp hV]
  ring

end Conservation

theorem Conservation.statement_holds : Conservation.Statement := by
  unfold Conservation.Statement ConservationStatement
  intro K _ ι _ I hI P n L p hP hL hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : IsSmoothHerm (constLine (ι := ι) (-Real.log p)) := contDiffOn_const
  have ha : ∀ k, (constLine (ι := ι) (-Real.log p)).a k = ((0 : K → ℕ) k : ℤ) := fun _ => rfl
  have hpot : (fun j z => Real.log ((L j).h z)) = pot L := rfl
  constructor
  · rw [hI.2.2 P n L _ (C (p : ℤ)) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 (by exact_mod_cast hp.ne_zero))]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C (p : ℤ)) = fun _ => 0 := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ / Real.exp (-(-Real.log p))) = 0
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [hp0.ne']
    unfold recR vertR arInt
    rw [hlog, Conservation.ptsIntegral_const, zero_mul, sub_zero]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [if_neg (Conservation.not_horizontal hp hW), if_neg (Conservation.not_horizontal hp hW)]
  · rw [hI.2.2 P n L _ (C 1) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 one_ne_zero)]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C 1) = fun _ => -Real.log p := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C 1))‖ / Real.exp (-(-Real.log p))) = _
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [Real.log_inv]
    have hempty : divSupp P (C 1 : MRing ι) = ∅ := by
      ext W
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hW
      have hle := hW.1.1.2
      rw [C_1, Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
      exact hW.1.1.1.ne_top hle
    unfold recR arInt
    rw [hempty, finsum_mem_empty, hlog, Conservation.ptsIntegral_const, hpot]
    ring

theorem Conservation.conservation_degree_form_of_existence (hE : ThmIExists.Statement) (hC : Conservation.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement := by
  intro K _ ι _ P n L p hP hL hp
  obtain ⟨I, hI⟩ := hE
  obtain ⟨h1, h2⟩ := hC K ι (I K ι) (hI K ι) P n L p hP hL hp
  have h := h1.symm.trans h2
  rw [Conservation.vertR_C_prime P L hp] at h
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' h

theorem Conservation.conservation_iff_degree_statement :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement ↔ DegreeStatement := by
  constructor
  · intro h K _ ι _ P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
    exact (h K ι P e L p hP hL hp).symm
  · intro h K _ ι _ P e L p hP hL hp
    have h' := h K ι P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at h'
    exact h'.symm

end GroundTheory.Heights₂.Heights.Inter
