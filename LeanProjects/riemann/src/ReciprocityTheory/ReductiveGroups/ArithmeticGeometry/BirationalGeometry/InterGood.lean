import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodG

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then c else 1) * z p

theorem eval_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) =
      c ^ a k0 * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ f.support := MvPolynomial.support_map_subset _ _ hm
  have hdeg := hf m hm' k0
  simp only [scaleBlock, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ x : (Σ k, ι k), (if x.1 = k0 then c else 1) ^ m x = c ^ a k0 := by
    rw [Fintype.prod_sigma, Finset.prod_eq_single k0]
    · simp [hdeg, Finset.prod_pow_eq_pow_sum]
    · intro k _ hk
      simp [hk]
    · simp
  rw [hc]
  ring

theorem scaleBlock_mem_zeroLocus (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (k0 : K) {c : ℂ} (hc : c ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : scaleBlock k0 c z ∈ mcPts P := by
  obtain ⟨S, hS, rfl⟩ := hP
  show (∀ k, ∃ i, scaleBlock k0 c z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ Ideal.span S, eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, ?_⟩
    simp only [scaleBlock]
    split_ifs <;> simp [hc, hi]
  · have hle : Ideal.span S ≤ RingHom.ker ((eval (scaleBlock k0 c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply]
      rw [eval_scaleBlock k0 c z s a ha, hz.2 s (Ideal.subset_span hs), mul_zero]
    exact (RingHom.mem_ker).mp (hle hf)

def evQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P →+* ℂ :=
  Ideal.Quotient.lift (qIdeal P) (eval₂Hom (algebraMap ℚ ℂ) z) fun a ha => by
    have hle : qIdeal P ≤ RingHom.ker (eval₂Hom (algebraMap ℚ ℂ) z) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, eval₂_map]
      have h := hz.2 f hf
      rw [eval_map] at h
      convert h using 2
      exact RingHom.ext_int _ _
    exact hle ha

theorem evQ_mk (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (q : MvPolynomial (Σ k, ι k) ℚ) :
    evQ P z hz (Ideal.Quotient.mk _ q) = eval₂ (algebraMap ℚ ℂ) z q := rfl

theorem goodProjExists : GoodProjExistsStatement := by
  intro K _ ι _ P e hP
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) (segQ P) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent P e hP hr L)
  have hint : ∀ t, ∃ p : Polynomial (MvPolynomial (Fin r) ℚ), p.Monic ∧
      Polynomial.eval₂ (aeval (forms (segQ P) L)).toRingHom (segQ P t) p = 0 := hL
  choose p hpm hpe using hint
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => if h : j.val < r then ∑ t, algebraMap ℚ ℂ (L ⟨j.val, h⟩ t) * w t else 0
      map_add' := by
        intro w w'
        funext j
        simp only [Pi.add_apply]
        split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  have hΨ : ∀ w (j : Fin r), Ψ w ⟨j.1, lt_of_lt_of_le j.2 hr⟩ = ∑ t, algebraMap ℚ ℂ (L j t) * w t := by
    intro w j
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta]
  have hA : ∀ z' (hz' : z' ∈ mcPts P), Ψ (segre z') = 0 →
      ∀ t, ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot (segre z' t) := by
    intro z' hz' h0 t
    have hφs : ∀ t', evQ P z' hz' (segQ P t') = segre z' t' := by
      intro t'
      show evQ P z' hz' (Ideal.Quotient.mk _ (segMon t')) = _
      rw [evQ_mk]
      simp [segMon, segre, eval₂_prod]
    have hφf : ∀ j, evQ P z' hz' (forms (segQ P) L j) = 0 := by
      intro j
      have h1 := congrFun h0 ⟨j.1, lt_of_lt_of_le j.2 hr⟩
      rw [hΨ] at h1
      simp only [forms, map_sum, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap, hφs]
      simpa using h1
    have hcomp : (evQ P z' hz').comp (aeval (forms (segQ P) L)).toRingHom =
        (algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [RingHom.map_rat_algebraMap]
      · intro j
        simp [hφf]
    show Polynomial.eval (segre z' t) ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)) = 0
    rw [Polynomial.eval_map, ← hcomp, ← hφs, ← Polynomial.hom_eval₂, hpe t, map_zero]
  refine ⟨Ψ, fun z hz h0 => ?_⟩
  obtain ⟨k0⟩ := hP.1
  have hhom : IsMultiHomogIdeal P := hP.2.1.2.1
  choose t0 ht0 using hz.1
  have hs : segre z t0 ≠ 0 := by
    simp only [segre]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => ht0 k
  have hsegA : ∀ c : ℂ, segre (scaleBlock k0 c z) = c • segre z := by
    intro c
    funext t
    simp only [segre, scaleBlock, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ k0 (fun _ => c)]
    simp
  have hroot : ∀ n : ℕ, ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot
      (((n : ℂ) + 1) * segre z t0) := by
    intro n
    have hcn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hmem : scaleBlock k0 ((n : ℂ) + 1) z ∈ mcPts P := scaleBlock_mem_zeroLocus P hhom k0 hcn hz
    have h0' : Ψ (segre (scaleBlock k0 ((n : ℂ) + 1) z)) = 0 := by
      rw [hsegA, map_smul, h0, smul_zero]
    have h5 := hA (scaleBlock k0 ((n : ℂ) + 1) z) hmem h0' t0
    have h7 : segre (scaleBlock k0 ((n : ℂ) + 1) z) t0 = ((n : ℂ) + 1) * segre z t0 := by
      rw [hsegA, Pi.smul_apply, smul_eq_mul]
    rw [h7] at h5
    exact h5
  have hinf := Set.infinite_of_injective_forall_mem
    (s := {x | ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot x})
    (f := fun n : ℕ => ((n : ℂ) + 1) * segre z t0)
    (by
      intro a b hab
      simp only at hab
      have h6 := mul_right_cancel₀ hs hab
      exact_mod_cast add_right_cancel h6) hroot
  exact hinf (Polynomial.finite_setOf_isRoot ((hpm t0).map _).ne_zero)

end

end ReciprocityTheory.ChartRestriction.G.Geo
