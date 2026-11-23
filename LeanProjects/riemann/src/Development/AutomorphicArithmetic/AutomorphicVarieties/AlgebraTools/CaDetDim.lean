import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.dim_quot_le_of_primes {P : Type} [CommRing P] (I J : Ideal P)
    (h : ∀ p : Ideal P, p.IsPrime → J ≤ p → I ≤ p) :
    ringKrullDim (P ⧸ J) ≤ ringKrullDim (P ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have hsub : PrimeSpectrum.zeroLocus (R := P) (J : Set P) ⊆ PrimeSpectrum.zeroLocus (I : Set P) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus] at hq ⊢
    exact h q.asIdeal q.isPrime hq
  exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) (fun a b hab => hab)

theorem UpperTheory.V.AlgebraTools.dim_relIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ringKrullDim (P ⧸ relIdeal z m) + (Fintype.card ι : ℕ) ≤ ringKrullDim P := by
  classical
  intro P _ _ ι _ _ z m hx
  set x : ι × ι ⊕ ι → P := Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m with hxdef
  let K : Ideal P := Ideal.span (Set.range x)
  let g : ι × ι → P := fun ij => z ij.1 ij.2 - if ij.1 = ij.2 then m ij.1 else 0
  let G : Ideal P := Ideal.span (Set.range g)
  have hreg := (regular_quotient_cotInd P (ι × ι ⊕ ι) x hx).2.1
  rw [Fintype.card_sum, Fintype.card_prod] at hreg
  have hA : ringKrullDim (P ⧸ relIdeal z m ⊔ G) ≤ ringKrullDim (P ⧸ K) := by
    apply dim_quot_le_of_primes
    intro q hq hle
    have hrel : relIdeal z m ≤ q := le_trans le_sup_left hle
    have hG : G ≤ q := le_trans le_sup_right hle
    have hg : ∀ ij, g ij ∈ q := fun ij => hG (Ideal.subset_span ⟨ij, rfl⟩)
    have hm : ∀ i, m i ∈ q := by
      intro i
      have h1 : z.mulVec m i ∈ q := hrel (Ideal.subset_span ⟨i, rfl⟩)
      have h2 : m i * m i = z.mulVec m i - ∑ j, g (i, j) * m j := by
        simp only [g, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
      have h3 : m i * m i ∈ q := by
        rw [h2]
        exact q.sub_mem h1 (q.sum_mem fun j _ => q.mul_mem_right _ (hg (i, j)))
      rcases hq.mem_or_mem h3 with h | h <;> exact h
    rw [Ideal.span_le]
    rintro _ ⟨(⟨i, j⟩ | i), rfl⟩
    · have h4 : z i j = g (i, j) + (if i = j then m i else 0) := by simp [g]
      show z i j ∈ q
      rw [h4]
      refine q.add_mem (hg _) ?_
      split_ifs
      · exact hm i
      · exact q.zero_mem
    · exact hm i
  have hB : ringKrullDim (P ⧸ relIdeal z m) ≤
      ringKrullDim (P ⧸ K) + ((Fintype.card ι * Fintype.card ι : ℕ) : WithBot ℕ∞) := by
    let Gb : Ideal (P ⧸ relIdeal z m) := G.map (Ideal.Quotient.mk _)
    have hsf : Gb.spanFinrank ≤ Fintype.card ι * Fintype.card ι := by
      have e : Gb = Ideal.span (Set.range (Ideal.Quotient.mk (relIdeal z m) ∘ g)) := by
        simp only [Gb, G, Ideal.map_span, Set.range_comp]
      rw [e]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      rw [← Set.image_univ, ← Finset.coe_univ]
      exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
    have hdim : ringKrullDim (P ⧸ relIdeal z m) ≤
        ringKrullDim ((P ⧸ relIdeal z m) ⧸ Gb) + Gb.spanFinrank := by
      rw [ringKrullDim_le_iff_isMaximal_height_le]
      intro M hM
      apply height_le_ringKrullDim_quotient_add_spanFinrank
      rw [Ideal.map_le_iff_le_comap]
      have hc : Ideal.comap (Ideal.Quotient.mk (relIdeal z m)) M = maximalIdeal P :=
        IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [hc, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hz : z i j ∈ maximalIdeal P := hx.mem (Sum.inl (i, j))
      have hmi : m i ∈ maximalIdeal P := hx.mem (Sum.inr i)
      show z i j - (if i = j then m i else 0) ∈ maximalIdeal P
      refine (maximalIdeal P).sub_mem hz ?_
      split_ifs
      · exact hmi
      · exact (maximalIdeal P).zero_mem
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup (relIdeal z m) G)] at hdim
    exact hdim.trans (add_le_add hA (by exact_mod_cast hsf))
  rw [← hreg]
  refine (add_le_add hB le_rfl).trans (le_of_eq ?_)
  rw [add_assoc]
  norm_cast
