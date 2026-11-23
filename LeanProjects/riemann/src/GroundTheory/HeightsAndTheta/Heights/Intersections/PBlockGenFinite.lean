import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGenFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem eval_map_rename (v : (Σ k, ι k) → (Σ k', ι' k')) (s : MRing ι) (z' : (Σ k', ι' k') → ℂ) :
    eval z' (map (Int.castRingHom ℂ) (rename v s)) = eval (fun p ↦ z' (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

end BlockGenFinite

open BlockGenFinite in

theorem BlockGenFinite.proof (hR : BlockRatioAlg.Statement) : BlockGenFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP
  have hrel := hP'.2.1.2.2
  have hpr := hP'.2.1.1
  have hrel' : ∀ k : FibreBlock κ, ∃ i : ι' k.1, (X (⟨k.1, i⟩ : Σ k', ι' k') : MRing ι') ∉ P' := fun k ↦ hrel k.1
  choose c hc using hrel'
  have hA := fun q : (Σ k : FibreBlock κ, ι' k.1) ↦
    hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ ⟨q.1.1, c q.1⟩ rfl (hc q.1)
  choose m A a hAh hAl hAP using hA
  refine ⟨(∏ q, rename v (A q (Fin.last (m q)))) * ∏ k : FibreBlock κ, X ⟨k.1, c k⟩,
    (∑ q, Function.extend κ (a q) 0) + ∑ k : FibreBlock κ, Pi.single k.1 1, ?_, ?_, ?_⟩
  · exact AvoidRing.isMultiHomog_mul
      (AvoidRing.isMultiHomog_prod _ _ _ fun q _ ↦ ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hAh q _))
      (AvoidRing.isMultiHomog_prod _ _ _ fun k _ ↦ AvoidRing.isMultiHomog_X _ _)
  · intro h
    rcases hpr.mul_mem_iff_mem_or_mem.mp h with h | h
    · obtain ⟨q, -, hq⟩ := hpr.prod_mem_iff.mp h
      exact hAl q hq
    · obtain ⟨k, -, hk⟩ := hpr.prod_mem_iff.mp h
      exact hc k hk
  intro u

  obtain ⟨pol, hpol⟩ : ∃ pol : (Σ k : FibreBlock κ, ι' k.1) → Polynomial ℂ, ∀ q, pol q =
      ∑ j : Fin (m q + 1), Polynomial.C (eval u (map (Int.castRingHom ℂ) (A q j))) * Polynomial.X ^ (j : ℕ) :=
    ⟨_, fun _ ↦ rfl⟩

  obtain ⟨build, hbuild⟩ : ∃ build : ((Σ k : FibreBlock κ, ι' k.1) → ℂ) → (Σ k', ι' k') → ℂ, ∀ ρ p',
      build ρ p' = if h : p'.1 ∈ Set.range κ then u (hv.2.2.2 p' h).choose else ρ ⟨⟨p'.1, h⟩, p'.2⟩ :=
    ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨(Fintype.piFinset fun q ↦ (pol q).roots.toFinset).image build, ?_⟩
  rintro z' hz' hf0 ⟨d, hd, hzd⟩
  have hzd' : ∀ p, z' (v p) = d p.1 * u p := fun p ↦ congrFun hzd p
  simp only [map_mul, map_prod, map_X, eval_X] at hf0
  have hcz : ∀ k : FibreBlock κ, z' ⟨k.1, c k⟩ ≠ 0 := fun k ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf0) k (Finset.mem_univ _)
  have hlead : ∀ q, eval u (map (Int.castRingHom ℂ) (A q (Fin.last (m q)))) ≠ 0 := by
    intro q h
    have := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf0) q (Finset.mem_univ _)
    rw [eval_map_rename, show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd,
      eval_smul_of_isMultiHomog (hAh q _), h, mul_zero] at this
    exact this rfl

  have hroot : ∀ q, z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩ ∈ (pol q).roots.toFinset := by
    intro q
    have hne : pol q ≠ 0 := by
      intro h0
      have h1 := congrArg (fun f ↦ Polynomial.coeff f (m q)) h0
      simp only [hpol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single (Fin.last (m q))] at h1
      · simp only [Fin.val_last, if_true] at h1
        exact hlead q h1
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (by simp [e]))
      · simp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hrel0 := hz'.2 _ (hAP q)
    simp only [map_sum, map_mul, map_pow, map_X, eval_X, eval_map_rename,
      show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd, eval_smul_of_isMultiHomog (hAh q _)] at hrel0
    have hD : (∏ k, d k ^ a q k) * z' ⟨q.1.1, c q.1⟩ ^ m q ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k)) (pow_ne_zero _ (hcz q.1))
    refine (mul_eq_zero.mp ?_).resolve_left hD
    rw [hpol, Polynomial.eval_finsetSum, Finset.mul_sum, ← hrel0]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (j : ℕ) ≤ m q := Nat.lt_succ_iff.mp j.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← pow_sub_mul_pow (z' ⟨q.1.1, c q.1⟩) hj, div_pow]
    field_simp [pow_ne_zero _ (hcz q.1)]

  refine ⟨build fun q ↦ z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩,
    Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hroot), ?_⟩
  refine ⟨fun k' ↦ if h : k' ∈ Set.range κ then d h.choose else z' ⟨k', c ⟨k', h⟩⟩,
    fun k' ↦ ?_, funext fun p' ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hd _
    · exact hcz ⟨k', h⟩
  · rw [hbuild]
    by_cases h : p'.1 ∈ Set.range κ
    · rw [dif_pos h]
      dsimp only
      rw [dif_pos h]
      obtain ⟨p, rfl⟩ := hv.2.2.2 p' h
      rw [show h.choose = p.1 from hv.1 (h.choose_spec.trans (hv.2.2.1 p)),
        show (hv.2.2.2 (v p) h).choose = p from hv.2.1 (hv.2.2.2 (v p) h).choose_spec]
      exact hzd' p
    · rw [dif_neg h]
      dsimp only
      rw [dif_neg h]
      have hc' := hcz ⟨p'.1, h⟩
      dsimp only at hc'
      field_simp [hc']

end GroundTheory.Heights₂.Heights.Inter
