import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_le_ker :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (D : Type) [CommRing D] [IsLocalRing D] (φ : P →+* D) [IsLocalHom φ] (l : ι → D),
      l c = 1 → (z.map φ).mulVec l = 0 → (∀ j, φ (m j) = l j * φ (m c)) → genKer z m c ≤ RingHom.ker φ := by
  intro P _ _ ι _ _ z m hcot c D _ _ φ _ l hlc hzl hm
  let ψ : MvPolynomial ι P →+* D := MvPolynomial.eval₂Hom φ l
  have hψC : ∀ a, ψ (MvPolynomial.C a) = φ a := fun a => MvPolynomial.eval₂Hom_C φ l a
  have hlam : ∀ j, ψ (UpperTheory.V.AlgebraTools.lam P c j) = l j := by
    intro j
    unfold UpperTheory.V.AlgebraTools.lam
    split_ifs with h
    · subst h
      simp [hlc]
    · exact MvPolynomial.eval₂Hom_X' φ l j
  let M0 : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P)
  haveI hM0 : M0.IsPrime := UpperTheory.V.AlgebraTools.isPrime_map_C (maximalIdeal P)
  let Q : Ideal (MvPolynomial ι P) := Ideal.comap ψ (maximalIdeal D)
  haveI : Q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal D)
  have hMQ : M0 ≤ Q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show ψ (MvPolynomial.C a) ∈ maximalIdeal D
    rw [hψC]
    exact map_nonunit φ a ha
  have hker : chartIdeal z m c ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ψ (((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i) = 0
      have h := congrFun hzl i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
      rw [map_sum]
      simp only [map_mul, hψC, hlam]
      exact h
    · show ψ (MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c)) = 0
      rw [map_sub, map_mul, hψC, hψC, hlam, hm j, sub_self]
  have hchartM : chartIdeal z m c ≤ M0 := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i ∈ M0
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      simpa using hcot.mem (Sum.inl (i, j))
    · show MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c) ∈ M0
      refine Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_))
      · simpa using hcot.mem (Sum.inr j)
      · simpa using hcot.mem (Sum.inr c)
  have hprime := UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime P ι z m hcot c Q hMQ
  have hsat : ∀ x, algebraMap (MvPolynomial ι P) (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) (chartIdeal z m c) →
      ∃ t ∉ Q, t * x ∈ chartIdeal z m c := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl)
      (S := Localization.AtPrime Q) (chartIdeal z m c) x).mp hx
    exact ⟨t, ht, htx⟩
  intro f hf
  obtain ⟨s, hs, hsf⟩ := hf
  have hmem := Ideal.mem_map_of_mem (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) hsf
  rw [map_mul] at hmem
  rcases hprime.mem_or_mem hmem with h | h
  · exfalso
    obtain ⟨t, ht, hts⟩ := hsat s h
    rcases hM0.mem_or_mem (hchartM hts) with h' | h'
    · exact ht (hMQ h')
    · exact hs h'
  · obtain ⟨t, ht, htf⟩ := hsat _ h
    have h0 : ψ (t * MvPolynomial.C f) = 0 := hker htf
    rw [map_mul, hψC] at h0
    have hu : IsUnit (ψ t) := by
      by_contra hn
      exact ht ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    exact (RingHom.mem_ker).mpr ((hu.mul_right_eq_zero).mp h0)
