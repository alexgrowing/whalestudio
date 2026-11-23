import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerOrder

theorem finrank_le_pow_of_aeval_surjective {n d : ℕ} {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (x : Fin d → A) (hsurj : Function.Surjective (MvPolynomial.aeval (R := K) x))
    (hpow : ∀ i, x i ^ n = 0) :
    Module.finrank K A ≤ n ^ d := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  let v : (Fin d → Fin n) → A := fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by
    intro m
    by_cases hm : ∀ i, m i < n
    · refine Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩
      have : e (fun i => ⟨m i, hm i⟩) = m := by
        ext i; simp [e]
      simp only [v, this]
    · push_neg at hm
      obtain ⟨i, hi⟩ := hm
      have h0 : MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) = 0 := by
        rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
        by_cases hmi : m i = 0
        · have hn : n = 0 := by omega
          subst hn
          have h10 : (1 : A) = 0 := by simpa using hpow i
          rw [← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]
        · apply Finset.prod_eq_zero (i := i) (by simpa using hmi)
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hi
          rw [hr, pow_add, hpow i, zero_mul]
      rw [h0]; exact Submodule.zero_mem _
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨P, rfl⟩ := hsurj y
    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : MvPolynomial.monomial m (MvPolynomial.coeff m P) =
        MvPolynomial.coeff m P • MvPolynomial.monomial m (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have h1 := finrank_range_le_card (R := K) v
  rw [Set.finrank, htop, finrank_top] at h1
  simpa using h1

theorem finrank_le_pow_finrank_cot (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  haveI := isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π := Ideal.Quotient.mkₐ K J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective K J
  have hε : (counitAlgHom K (H ⧸ J)).comp π = counitAlgHom K H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p K H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom K (H ⧸ J) with hεdef
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hpow : ∀ f ∈ RingHom.ker ε, f ^ p = 0 := by
    intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := K) hf)
  have : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      y - ∑ i, l i • (x i : H ⧸ J) ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  exact finrank_le_pow_of_aeval_surjective (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil _ (fun i => (x i).2) hspan)
    (fun i => hpow _ (x i).2)

end GlobalTheory.PDiv.FrobKerOrder
