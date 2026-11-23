import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra TensorProduct

namespace GlobalTheory.PDiv.FrobKerOrder

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]; simp

theorem cast_eq_zero_of_algebra (p : ℕ) (k A : Type*) [CommRing k] [CharP k p] [CommRing A]
    [Algebra k A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]

variable (p : ℕ) [hp : Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H]
  [HopfAlgebra k H]

theorem mk_pow_eq (x : H) :
    Ideal.Quotient.mkₐ k (frobKerIdeal p k H) x ^ p =
      algebraMap k _ (counit (R := k) x) ^ p := by
  have hx : x - algebraMap k H (counit (R := k) x) ∈ augIdeal k H := by
    simp [RingHom.mem_ker]
  have h0 : Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      ((x - algebraMap k H (counit (R := k) x)) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have e : x = (x - algebraMap k H (counit (R := k) x)) + algebraMap k H (counit (R := k) x) := by
    ring
  conv_lhs => rw [e, ← map_pow, add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k H),
    map_add, h0, zero_add, map_pow, AlgHom.commutes]

theorem map_pow_eq (t : H ⊗[k] H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
      (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)) t ^ p =
    (1 : H ⧸ frobKerIdeal p k H) ⊗ₜ[k] (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      (TensorProduct.lid k H (LinearMap.rTensor H (counit (R := k) (A := H)) t)) ^ p) := by
  induction t with
  | zero => simp [hp.out.ne_zero]
  | add x y hx hy =>
    simp only [map_add]
    rw [add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _),
      add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _), hx, hy, tmul_add]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, mk_pow_eq,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
      Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem isHopfIdeal : (frobKerIdeal p k H).IsHopfIdeal k where
  counit_eq_zero x hx := frobKerIdeal_le_augIdeal hp.out.ne_zero k H hx
  map_mkQ_comul_eq_zero x hx := by
    have h : frobKerIdeal p k H ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
          (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))).comp (comulAlgHom k H)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, map_pow_eq,
        comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
      have : Ideal.Quotient.mkₐ k (frobKerIdeal p k H) (a ^ p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
      rw [this, tmul_zero]
    exact h hx
  antipode_mem x hx := by
    have h : frobKerIdeal p k H ≤ (frobKerIdeal p k H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
      apply pow_mem_frobKerIdeal
      have ha' : counit (R := k) a = 0 := ha
      simp [RingHom.mem_ker, ha']
    exact h hx

omit [CharP k p] in
theorem le_sq : frobKerIdeal p k H ≤ augIdeal k H ^ 2 := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow ha p)

theorem pow_le_finrank {n d : ℕ} {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : Fin d → A)
    (h : RingHom.ker (MvPolynomial.aeval (R := K) x) =
      Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n)) :
    n ^ d ≤ Module.finrank K A := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  have he : Function.Injective e := by
    intro a b hab
    funext i
    have := DFunLike.congr_fun hab i
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a : Fin d → Fin n =>
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hmem : (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) ∈
        RingHom.ker (MvPolynomial.aeval (R := K) x) := by
      rw [RingHom.mem_ker, map_sum]
      simpa only [map_smul] using hg
    have hr : (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n) =
        (fun s => MvPolynomial.monomial s (1 : K)) '' Set.range (fun i => Finsupp.single i n) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [MvPolynomial.X_pow_eq_monomial]
    rw [h, hr, MvPolynomial.mem_ideal_span_monomial_image] at hmem
    by_contra hne
    have hc : MvPolynomial.coeff (e a) (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) = g a := by
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff]
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem (e a) (by rw [MvPolynomial.mem_support_iff, hc]; exact hne)
    have h1 := hi i
    have h2 := (a i).2
    simp [e] at h1
    omega
  simpa using hli.fintype_card_le_finrank

theorem pow_finrank_cot_le [Module.Finite k H] :
    p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  haveI := isHopfIdeal p k H
  set J := frobKerIdeal p k H with hJ
  let π := Ideal.Quotient.mkₐ k J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k J
  have hε : (counitAlgHom k (H ⧸ J)).comp π = counitAlgHom k H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p k H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom k (H ⧸ J) with hεdef
  let b := Module.finBasis k (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  refine pow_le_finrank (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.truncated_polynomial p k (H ⧸ J) _ _ ?_ (fun i => (x i).2) ?_ ?_).2
  · intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := k) hf)
  · intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  · intro l hl
    have h1 : AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i

end GlobalTheory.PDiv.FrobKerOrder
