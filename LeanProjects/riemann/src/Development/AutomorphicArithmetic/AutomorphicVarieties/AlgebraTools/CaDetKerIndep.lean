import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.generic_kernel_monotone
    (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι P) (m : ι → P)
    (h : CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m)) (c d : ι) :
    genKer z m c ≤ genKer z m d := by
  classical
  intro f hf
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C (ι := ι) (maximalIdeal P)
  set Q : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P) with hQdef
  let L := Localization.AtPrime Q
  let J : Ideal L := Ideal.map (algebraMap (MvPolynomial ι P) L) (chartIdeal z m d)
  haveI hJ : J.IsPrime := chartIdeal_localization_isPrime P ι z m h d Q le_rfl
  haveI : IsLocalRing (L ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let ψ : MvPolynomial ι P →+* L ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap (MvPolynomial ι P) L)
  let φ : P →+* L ⧸ J := ψ.comp MvPolynomial.C
  have hJle : J ≤ maximalIdeal L := IsLocalRing.le_maximalIdeal hJ.ne_top
  have hψ : ∀ g ∈ chartIdeal z m d, ψ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  haveI : IsLocalHom φ := by
    constructor
    intro p hp
    by_contra hpu
    have hpm : p ∈ maximalIdeal P := (IsLocalRing.mem_maximalIdeal p).2 hpu
    have hC : (MvPolynomial.C p : MvPolynomial ι P) ∈ Q := Ideal.mem_map_of_mem _ hpm
    have hL : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q _).2 hC
    obtain ⟨u, hu⟩ := hp
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : L ⧸ J)
    have h1 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy]
      have hu' : Ideal.Quotient.mk J (algebraMap (MvPolynomial ι P) L (MvPolynomial.C p)) = ↑u :=
        hu.symm
      rw [hu', Units.mul_inv, sub_self]
    have h3 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y ∈ maximalIdeal L :=
      Ideal.mul_mem_right _ _ hL
    have h4 : (1 : L) ∈ maximalIdeal L := by
      have h5 := Ideal.sub_mem _ h3 (hJle h1)
      simpa using h5
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  let l : ι → L ⧸ J := fun j => ψ (lam P d j)
  have hl : l d = 1 := by
    show ψ (lam P d d) = 1
    simp [lam]
  have hmul : (z.map φ).mulVec l = 0 := by
    funext i
    have hmem : (z.map MvPolynomial.C).mulVec (lam P d) i ∈ chartIdeal z m d :=
      Ideal.subset_span ⟨Sum.inl i, rfl⟩
    have h0 := hψ _ hmem
    rw [RingHom.map_mulVec, Matrix.map_map] at h0
    exact h0
  have hm : ∀ j, φ (m j) = l j * φ (m d) := by
    intro j
    by_cases hj : j = d
    · subst hj
      rw [hl, one_mul]
    · have hmem : MvPolynomial.C (m j) - lam P d j * MvPolynomial.C (m d) ∈ chartIdeal z m d :=
        Ideal.subset_span ⟨Sum.inr ⟨j, hj⟩, rfl⟩
      have h0 := hψ _ hmem
      rw [map_sub, map_mul, sub_eq_zero] at h0
      exact h0
  have hlamc : lam P d c ∉ Q := by
    rw [hQdef, MvPolynomial.mem_map_C_iff]
    intro hall
    by_cases hcd : c = d
    · have h0 := hall 0
      rw [show lam P d c = 1 from if_pos hcd, MvPolynomial.coeff_zero_one] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
    · have h0 := hall (Finsupp.single c 1)
      rw [show lam P d c = MvPolynomial.X c from if_neg hcd, MvPolynomial.coeff_X, if_pos rfl] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
  have hunitL : IsUnit (algebraMap (MvPolynomial ι P) L (lam P d c)) :=
    IsLocalization.map_units L (⟨lam P d c, hlamc⟩ : Q.primeCompl)
  have hunit : IsUnit (l c) := hunitL.map (Ideal.Quotient.mk J)
  set w : L ⧸ J := ↑hunit.unit⁻¹ with hwdef
  have hw : w * l c = 1 := hunit.val_inv_mul
  let l' : ι → L ⧸ J := fun j => w * l j
  have hl' : l' c = 1 := hw
  have hmul' : (z.map φ).mulVec l' = 0 := by
    funext i
    have h7 := congrFun hmul i
    simp only [l', Matrix.mulVec, dotProduct, Pi.zero_apply] at h7 ⊢
    simp_rw [mul_left_comm _ w]
    rw [← Finset.mul_sum, h7, mul_zero]
  have hm' : ∀ j, φ (m j) = l' j * φ (m c) := by
    intro j
    show φ (m j) = w * l j * φ (m c)
    rw [hm c, hm j]
    calc l j * φ (m d) = l j * φ (m d) * (w * l c) := by rw [hw, mul_one]
      _ = w * l j * (l c * φ (m d)) := by ring
  have hk := genKer_le_ker P ι z m h c (L ⧸ J) φ l' hl' hmul' hm' hf
  rw [RingHom.mem_ker] at hk
  have hfJ : algebraMap (MvPolynomial ι P) L (MvPolynomial.C f) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.1 hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).1 hfJ
  simp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl L] at hx
  obtain ⟨⟨t, ht⟩, htx⟩ := hx
  simp only at htx
  refine ⟨t * s, ?_, ?_⟩
  · exact Q.primeCompl.mul_mem ht hs
  · have h6 : t * s * MvPolynomial.C f = t * a := by rw [← htx]; ring
    rw [h6]
    exact Ideal.mul_mem_left _ _ ha

theorem UpperTheory.V.AlgebraTools.genKer_eq :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c d : ι, genKer z m c = genKer z m d := by
  intro P _ _ ι _ _ z m h c d
  exact le_antisymm (generic_kernel_monotone P ι z m h c d) (generic_kernel_monotone P ι z m h d c)
