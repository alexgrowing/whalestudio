import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem PrimeFiltration.Irrelevant.proof : PrimeFiltration.Irrelevant.Statement.{u} := by
  intro S _ _ N pp _ _ hX
  refine ⟨1, fun c hc f hf => ?_⟩
  have hle : Ideal.span ((X : Fin (N + 1) → Poly S N) '' Set.univ) ≤ pp := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact hX i
  apply hle
  rw [mem_ideal_span_X_image]
  intro m hm
  by_contra h
  push Not at h
  have hm0 : m = 0 := by
    ext i
    exact h i (Set.mem_univ _)
  have hdeg := hf (mem_support_iff.mp hm)
  rw [hm0] at hdeg
  simp at hdeg
  omega

section PointLemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem ideal_eq_of_isHomogeneous {I J : Ideal (Poly S N)}
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f.IsHomogeneous e → (f ∈ I ↔ f ∈ J)) : I = J := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact J.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mp (hI f hf d)
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact I.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mpr (hJ f hf d)

theorem exists_eq_X_pow_of_mem_monos_single {s : Poly S N} (hs : s ∈ monos {j}) :
    ∃ n : ℕ, s = X j ^ n := by
  have hs' : s ∈ Submonoid.closure {(X j : Poly S N)} := by
    have : ((fun i => (X i : Poly S N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X j} := by simp
    rw [← this]
    exact hs
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
  exact ⟨n, rfl⟩

theorem notMem_of_mem_monos_single {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hX : (X j : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos {j}) : s ∉ pp := by
  obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
  exact fun h => hX (hpp.mem_of_pow_mem n h)

theorem mem_of_div_eq (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {f s' G s : Poly S N} {e D : ℕ}
    (hf : f.IsHomogeneous e) (hs' : s' ∈ monos {j}) (hs'e : s'.IsHomogeneous e) (hG : G ∈ pp)
    (hGD : G.IsHomogeneous D) (hs : s ∈ monos {j}) (hsD : s.IsHomogeneous D)
    (h : aeval x f / aeval x s' = aeval x G / aeval x s) : f ∈ pp := by
  have h0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have h0' : aeval x s' ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs'
  rw [div_eq_div_iff h0' h0] at h
  have h2 : (s' * G).IsHomogeneous (D + e) := by
    rw [add_comm D e]
    exact hs'e.mul hGD
  have hF : s * f - s' * G ∈ primeOf (S := S) x := by
    rw [mem_primeOf_of_isHomogeneous x ((hsD.mul hf).sub h2)]
    simp only [map_sub, map_mul]
    linear_combination h
  have h3 : s * f ∈ pp := by
    have := pp.add_mem (hle hF) (pp.mul_mem_left s' hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem h3).resolve_left (notMem_of_mem_monos_single hX hs)

variable (x) in

def chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    Ideal (chartRing S x (singleChart hj)) where
  carrier := {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ pp ∧ s ∈ monos {j} ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ (a : Ω) = aeval x f / aeval x s}
  zero_mem' := ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
    by simp⟩
  add_mem' := by
    rintro a b ⟨f, s, e, hf, hs, hfe, hse, ha⟩ ⟨g, t, d, hg, ht, hgd, htd, hb⟩
    refine ⟨f * t + s * g, s * t, e + d, pp.add_mem (pp.mul_mem_right t hf) (pp.mul_mem_left s hg),
      mul_mem hs ht, (hfe.mul htd).add (hse.mul hgd), hse.mul htd, ?_⟩
    rw [Subalgebra.coe_add, ha, hb, div_add_div _ _ (eval_ne_zero_of_mem_monos (singleChart hj) hs)
      (eval_ne_zero_of_mem_monos (singleChart hj) ht)]
    simp only [map_add, map_mul]
  smul_mem' := by
    rintro c a ⟨g, t, d, hg, ht, hgd, htd, ha⟩
    obtain ⟨f, s, e, hs, hfe, hse, hc⟩ := c.2
    refine ⟨f * g, s * t, e + d, pp.mul_mem_left f hg, mul_mem hs ht, hfe.mul hgd, hse.mul htd, ?_⟩
    change (c : Ω) * (a : Ω) = _
    rw [hc, ha, map_mul, map_mul, div_mul_div_comm]

theorem chartPrime_le_chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    chartPrime pp hj ≤ chartPrimeIdeal x hj pp := by
  rw [chartPrime, Ideal.span_le]
  intro a ha
  exact ha

theorem mem_chartPrime_iff (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {a : chartRing S x (singleChart hj)}
    {f s : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s ∈ monos {j}) (hse : s.IsHomogeneous e)
    (ha : (a : Ω) = aeval x f / aeval x s) : a ∈ chartPrime pp hj ↔ f ∈ pp := by
  constructor
  · intro h
    obtain ⟨G, t, D, hG, ht, hGD, htD, hat⟩ := chartPrime_le_chartPrimeIdeal hj pp h
    exact mem_of_div_eq hj hle hX hf hs hse hG hGD ht htD (ha.symm.trans hat)
  · intro h
    exact Ideal.subset_span ⟨f, s, e, h, hs, hf, hse, ha⟩

theorem coe_aeval_ratio (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) = aeval x f / x j ^ e := by
  rw [← aeval_div_of_isHomogeneous hf j]
  change (chartRing S x (singleChart hj)).val _ = _
  rw [comp_aeval_apply]
  rfl

theorem coe_aeval_ratio' (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) =
      aeval x f / aeval x (X j ^ e : Poly S N) := by
  rw [coe_aeval_ratio hj hf, map_pow, aeval_X]

end PointLemmas

theorem PrimeFiltration.Point.proof : PrimeFiltration.Point.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX
  refine ⟨?_, ?_⟩
  · rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      rw [mem_chartPrime_iff (f := 1) (s := 1) hj hle hX (isHomogeneous_one _ _) (one_mem _)
        (isHomogeneous_one _ _) (by simp)]
      exact (Ideal.ne_top_iff_one pp).mp hpp.ne_top
    · intro a b hab
      obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
      obtain ⟨g, t, d, ht, hg, htd, hb⟩ := b.2
      have hab' : ((a * b : chartRing S x (singleChart hj)) : Ω) = aeval x (f * g) / aeval x (s * t) := by
        rw [Subalgebra.coe_mul, ha, hb, map_mul, map_mul, div_mul_div_comm]
      rw [mem_chartPrime_iff hj hle hX (hf.mul hg) (mul_mem hs ht) (hse.mul htd) hab'] at hab
      rw [mem_chartPrime_iff hj hle hX hf hs hse ha, mem_chartPrime_iff hj hle hX hg ht htd hb]
      exact hpp.mem_or_mem hab
  · intro K' _ _ ψ hker
    apply ideal_eq_of_isHomogeneous (fun p hp d => homogeneousComponent_mem_primeOf _ hp d) hhom
    intro f e hf
    rw [mem_primeOf_of_isHomogeneous _ hf, ← comp_aeval_apply, ← RingHom.mem_ker, hker]
    exact mem_chartPrime_iff hj hle hX hf (pow_mem (X_mem_monos (Finset.mem_singleton_self j)) e)
      (isHomogeneous_X_pow j e) (coe_aeval_ratio' hj hf)

end

end GroundTheory.Heights₂.Heights.Kleiman
