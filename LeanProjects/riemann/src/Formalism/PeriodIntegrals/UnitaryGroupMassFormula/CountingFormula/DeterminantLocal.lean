import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountLeOfIntegral

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem determinant_local : DetLocal := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b a h𝔭 hJ P hP
  classical
  obtain ⟨hbX, hloc, horth, hdiag, ha0⟩ := hJ
  set S : Submonoid (𝓞 K) :=
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} with hSdef
  have hS1 : ∀ s ∈ S, s ∉ P.asIdeal := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨t, ht, rfl⟩ := hs
      intro hmem
      apply ht
      rw [← hP]
      exact hmem
    | one => exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    | mul s s' _ _ h1 h2 => exact fun hm => (P.isPrime.mem_or_mem hm).elim h1 h2
  have hS2 : ∀ s ∈ S, star ((s : 𝓞 K) : K) = (s : K) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨t, ht, rfl⟩ := hs
      exact (hfix _).2 ⟨(t : F), rfl⟩
    | one => simp
    | mul s s' _ _ h1 h2 =>
      rw [show ((s * s' : 𝓞 K) : K) = (s : K) * (s' : K) from rfl, star_mul', h1, h2]

  have hcard : Fintype.card ι = finrank K X := by rw [← hspan, finrank_span_eq_card hind]
  let σ : ι ≃ Fin (finrank K X) := Fintype.equivFinOfCardEq hcard
  set b' : ι → V := fun k => b (σ k) with hb'def
  have hb'X : ∀ k, b' k ∈ Submodule.span K (Set.range x) := fun k => hspan ▸ hbX (σ k)
  choose C0 hC0 using fun k => (Submodule.mem_span_range_iff_exists_fun K).mp (hb'X k)
  set C : Matrix ι ι K := fun i k => C0 k i with hCdef
  have hC : ∀ k, b' k = ∑ i, C i k • x i := fun k => (hC0 k).symm
  have hgb : gram h b' = C.conjTranspose * gram h x * C := gram_comb h x C b' hC
  have hgdiag : gram h b' = Matrix.diagonal fun k => algebraMap F K ((a (σ k) : 𝓞 F) : F) := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      simp [gram, hb'def, hdiag]
    · rw [Matrix.diagonal_apply_ne _ hkl]
      exact horth _ _ (σ.injective.ne hkl)
  have hdetb : algebraMap F K (∏ j, ((a j : 𝓞 F) : F)) = star C.det * C.det * (gram h x).det := by
    have e1 := congrArg Matrix.det hgb
    rw [hgdiag, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at e1
    rw [map_prod, mul_right_comm, ← e1]
    exact (Equiv.prod_comp σ (fun j => algebraMap F K ((a j : 𝓞 F) : F))).symm
  have ha0' : algebraMap F K (∏ j, ((a j : 𝓞 F) : F)) ≠ 0 := by
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [map_ne_zero_iff _ (algebraMap F K).injective]
    exact_mod_cast ha0 j
  have hCdet : C.det ≠ 0 := by
    intro h0; apply ha0'; rw [hdetb, h0]; simp
  have hsCdet : star C.det ≠ 0 := by
    intro h0; apply hCdet; rw [← star_star C.det, h0, star_zero]
  have hlocmem : ∀ v, v ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ↔ ∃ s ∈ S, s • v ∈ pbLat x 𝔞 := by
    intro v; rw [hloc]; exact Iff.rfl
  have hlocmem2 : ∀ v, v ∈ locF 𝔭 (pbLat x 𝔞) ↔ ∃ s ∈ S, s • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro v; rw [← hloc]; exact Iff.rfl
  have hcoeS : ∀ o : 𝓞 K, ∀ v : V, ((o : K)) • v = o • v := fun o v => algebraMap_smul K o v

  have ht0 : ∀ k, ∃ t ∈ S, t • b' k ∈ pbLat x 𝔞 := fun k =>
    (hlocmem (b' k)).mp ⟨1, S.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨σ k, rfl⟩⟩
  choose t htS htL using ht0
  have hrow : ∀ i k, C i k * (t k : K) ∈ 𝔞 i := by
    intro i k
    obtain ⟨c, hc, hcv⟩ := pb_coords x 𝔞 (htL k)
    have e2 : t k • b' k = ∑ i, (C i k * (t k : K)) • x i := by
      rw [hC k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcoeS, smul_smul, mul_comm]
    rw [e2] at hcv
    have := coords_unique hind hcv
    rw [congrFun this i]
    exact hc i
  have hM : (C * Matrix.diagonal fun k => (t k : K)).det ∈ ∏ i, 𝔞 i :=
    det_mem_prod 𝔞 _ fun i k => by rw [Matrix.mul_diagonal]; exact hrow i k
  rw [Matrix.det_mul, Matrix.det_diagonal] at hM
  have hT : (∏ k, t k) ∈ S := Submonoid.prod_mem S fun k _ => htS k
  have hTc : (∏ k, (t k : K)) = ((∏ k, t k : 𝓞 K) : K) := by
    rw [← map_prod (algebraMap (𝓞 K) K)]
  have hT0 : (∏ k, (t k : K)) ≠ 0 := by
    rw [hTc]; intro h0
    apply hS1 _ hT
    have : (∏ k, t k : 𝓞 K) = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem
  have hcT : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (∏ k, (t k : K))) = 0 := by
    rw [hTc]; exact count_span_unit P _ (hS1 _ hT)
  have hB1 : FractionalIdeal.count K P (∏ i, 𝔞 i) ≤
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) C.det) := by
    have := count_le_of_mem (K := K) P hM (mul_ne_zero hCdet hT0)
    rwa [count_span_mul P hCdet hT0, hcT, add_zero] at this
  have hB2 : FractionalIdeal.count K P (∏ i, 𝔞 i) ≤
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (star C.det)) := by
    have hsM := sStable_prod Finset.univ 𝔞 (fun i => hstar i) _ hM
    have hsT : star (∏ k, (t k : K)) = ∏ k, (t k : K) := by rw [hTc]; exact hS2 _ hT
    rw [star_mul', hsT] at hsM
    have := count_le_of_mem (K := K) P hsM (mul_ne_zero hsCdet hT0)
    rwa [count_span_mul P hsCdet hT0, hcT, add_zero] at this

  have hb'det : (gram h b').det ≠ 0 := by
    rw [hgdiag, Matrix.det_diagonal, Equiv.prod_comp σ (fun j => algebraMap F K ((a j : 𝓞 F) : F))]
    rw [← map_prod]; exact ha0'
  have hbind : LinearIndependent K b' := linearIndependent_of_det_gram h b' hb'det
  have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hCdet)
  have hx : ∀ i, x i = ∑ k, C⁻¹ k i • b' k := by
    intro i
    simp_rw [hC, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have e4 : ∀ j, ∑ k, C⁻¹ k i * C j k = (1 : Matrix ι ι K) j i := by
      intro j
      rw [← hCinv, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, e4, Matrix.one_apply]
    simp
  have hint2 : ∀ z : ι → K, (∀ i, z i ∈ 𝔞 i) → ∃ s ∈ S,
      (C.det)⁻¹ * (s : K) * ∏ i, z i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro z hz
    have h1 : ∀ i, ∃ s ∈ S, ∃ e : Fin (finrank K X) → 𝓞 K, ∑ j, e j • b j = s • (z i • x i) := by
      intro i
      have hm : z i • x i ∈ pbLat x 𝔞 := Submodule.subset_span ⟨i, z i, hz i, rfl⟩
      obtain ⟨s, hs, hsm⟩ := (hlocmem2 (z i • x i)).mp ⟨1, S.one_mem, by rw [one_smul]; exact hm⟩
      obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsm
      exact ⟨s, hs, e, he⟩
    choose s hsS e he using h1
    have hcoord : ∀ i k, ((e i (σ k) : 𝓞 K) : K) = C⁻¹ k i * ((s i : K) * z i) := by
      intro i k
      have e3 : ∑ k, ((e i (σ k) : 𝓞 K) : K) • b' k = ∑ k, (C⁻¹ k i * ((s i : K) * z i)) • b' k := by
        have l1 : ∑ k, ((e i (σ k) : 𝓞 K) : K) • b' k = ∑ j, e i j • b j := by
          rw [← Equiv.sum_comp σ (fun j => e i j • b j)]
          exact Finset.sum_congr rfl fun k _ => hcoeS _ _
        rw [l1, he i, hx i, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hcoeS, smul_smul, smul_smul]
        congr 1
        ring
      exact congrFun (coords_unique hbind e3) k
    refine ⟨∏ i, s i, Submonoid.prod_mem S fun i _ => hsS i, ?_⟩
    set Yo : Matrix ι ι (𝓞 K) := fun k i => e i (σ k) with hYo
    have hY : Yo.map (algebraMap (𝓞 K) K) = C⁻¹ * Matrix.diagonal fun i => (s i : K) * z i := by
      ext k i
      rw [Matrix.mul_diagonal]
      exact hcoord i k
    have hdY := congrArg Matrix.det hY
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdY
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨Yo.det, ?_⟩
    rw [hdY, Finset.prod_mul_distrib, ← map_prod (algebraMap (𝓞 K) K) s]
    ring

  choose y hyI hy0 hyc using fun i => exists_exact (K := K) P (hne i)
  have hprodc : FractionalIdeal.count K P (∏ i, 𝔞 i) = ∑ i, FractionalIdeal.count K P (𝔞 i) :=
    FractionalIdeal.count_prod K P _ _ (fun i _ => hne i)
  obtain ⟨s1, hs1, hw1⟩ := hint2 y hyI
  obtain ⟨s2, hs2, hw2⟩ := hint2 (fun i => star (y i)) (fun i => hstar i _ (hyI i))
  have hw2' : (star C.det)⁻¹ * (s2 : K) * ∏ i, y i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h3 := sStable_one (K := K) _ hw2
    have hsp : star (∏ i, star (y i)) = ∏ i, y i := by
      rw [← starRingEnd_apply, map_prod]
      simp [starRingEnd_apply]
    rwa [star_mul', star_mul', star_inv₀, hS2 s2 hs2, hsp] at h3
  have hA1 := count_le_of_integral P C.det s1 y hCdet (hS1 s1 hs1) hy0 hw1
  have hA2 := count_le_of_integral P (star C.det) s2 y hsCdet (hS1 s2 hs2) hy0 hw2'
  simp_rw [hyc] at hA1 hA2
  rw [← hprodc] at hA1 hA2

  have hp0 : (∏ i, 𝔞 i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  rw [hdetb, count_span_mul P (mul_ne_zero hsCdet hCdet) hdet, count_span_mul P hsCdet hCdet,
    FractionalIdeal.count_mul K P (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet),
    Finset.prod_pow, FractionalIdeal.count_pow]
  push_cast
  linarith

end PI.UnitaryGroupMassFormula.CntFormula.R6
