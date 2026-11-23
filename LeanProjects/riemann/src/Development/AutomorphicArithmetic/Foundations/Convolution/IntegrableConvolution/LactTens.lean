import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JUnique
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactGen
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Fx
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ}

private theorem prod_upd (φ : Fin (m + 1) → TI F n) (k : Fin (m + 1)) (x : TI F n)
    (c : Fin (m + 1) → archGroup F n) :
    ∏ i, (Function.update φ k x i) (c i) = x (c k) * ∏ i ∈ Finset.univ.erase k, φ i (c i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem tens_lin {φ : Fin (m + 1) → TI F n} {k : Fin (m + 1)} {x y : TI F n} {b c : TI E n}
    (r s : ℂ) (hx : IsTens D (Function.update φ k x) b) (hy : IsTens D (Function.update φ k y) c) :
    IsTens D (Function.update φ k (r • x + s • y)) (r • b + s • c) := by
  intro g
  have h1 := hx g
  have h2 := hy g
  rw [prod_upd] at h1 h2 ⊢
  simp only [CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply,
    smul_eq_mul, h1, h2]
  ring

end

private theorem zc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {τ : K →+* ℂ}
    {j : HarishChandra.U n →ₐ[ℂ] UC K n} (hj : IsJ τ j)
    (hu : ∀ j', IsJ τ j' → j' = j) (i : Fin n) :
    zc τ i = j ((HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ :
        Subalgebra.center ℂ (HarishChandra.U n)) := by
  obtain ⟨j', hj', h⟩ := Classical.epsilon_spec (p := fun z : UC K n => ∃ j, IsJ τ j ∧
    z = j ((HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ :
        Subalgebra.center ℂ (HarishChandra.U n))) ⟨_, j, hj, rfl⟩
  rw [hu j' hj'] at h
  exact h

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactTens :
    UpperTheory.ConvolutionTheory.L1.LactTens := by
  intro F E _ _ _ _ _ _ _ σ m D n τ k hk φ₀ β₀ hs₀ ht₀ i
  obtain ⟨⟨jE, hjE, uE⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.jUnique E n τ
  obtain ⟨⟨jF, hjF, uF⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.jUnique F n (τ.comp (algebraMap F E))
  have key : ∀ u : HarishChandra.U n, ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
      IsTens D (Function.update φ k (lact (jF u) (φ k))) (lact (jE u) β) := by
    have sm : ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → SmoothT β :=
      fun φ β hs ht => (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β ht).1 hs
    have halg : ∀ r : ℂ, ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
        IsTens D (Function.update φ k (lact (jF (algebraMap ℂ _ r)) (φ k))) (lact (jE (algebraMap ℂ _ r)) β) := by
      intro r φ β hs ht
      obtain ⟨-, h1, -, -, hc⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, h1', -, -, hc'⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hc, hc', h1, h1']
      intro g
      have h := ht g
      rw [prod_upd, CompactlySupportedContinuousMap.smul_apply, CompactlySupportedContinuousMap.smul_apply, h,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), smul_eq_mul, smul_eq_mul, mul_assoc]
    have hadd : ∀ a b : HarishChandra.U n,
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF a) (φ k))) (lact (jE a) β)) →
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF b) (φ k))) (lact (jE b) β)) →
        ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF (a + b)) (φ k))) (lact (jE (a + b)) β) := by
      intro a b ha hb φ β hs ht
      obtain ⟨-, -, -, hp, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, -, -, hp', -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      rw [map_add, map_add, hp, hp']
      simpa using tens_lin (D := D) 1 1 (ha φ β hs ht) (hb φ β hs ht)
    have hmul : ∀ a b : HarishChandra.U n,
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF a) (φ k))) (lact (jE a) β)) →
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF b) (φ k))) (lact (jE b) β)) →
        ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF (a * b)) (φ k))) (lact (jE (a * b)) β) := by
      intro a b ha hb φ β hs ht
      obtain ⟨-, -, hm, -, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨hsu, -, hm', -, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      have hs' : ∀ i, SmoothT (Function.update φ k (lact (jF b) (φ k)) i) := by
        intro i
        by_cases h : i = k
        · subst h; rw [Function.update_self]; exact hsu _
        · rw [Function.update_of_ne h]; exact hs i
      have := ha _ _ hs' (hb φ β hs ht)
      rw [Function.update_self, Function.update_idem] at this
      rw [map_mul, map_mul, hm, hm']
      exact this
    have hgen : ∀ (p : Fin n × Fin n) (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
        IsTens D (Function.update φ k (lact (jF (HarishChandra.e p)) (φ k))) (lact (jE (HarishChandra.e p)) β) := by
      rintro ⟨a, b⟩ φ β hs ht
      obtain ⟨-, -, -, hp, hc⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, -, -, hp', hc'⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      have form : ∀ {K : Type} [Field K] [NumberField K] (t : K →+* ℂ),
          (2⁻¹ : ℂ) ⊗ₜ[ℝ] elem t a b 1 - (2⁻¹ * Complex.I) ⊗ₜ[ℝ] elem t a b Complex.I =
            (2⁻¹ : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] elem t a b 1) + (-(2⁻¹ * Complex.I)) • ((1 : ℂ) ⊗ₜ[ℝ] elem t a b Complex.I) := by
        intro K _ _ t
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one,
          TensorProduct.neg_tmul, sub_eq_add_neg]
      rw [hjE a b, hjF a b, form, form, hp, hp', hc, hc, hc', hc']
      exact tens_lin (D := D) _ _ (UpperTheory.ConvolutionTheory.L1.lactGen F E σ m D n τ k hk φ β hs ht a b 1)
        (UpperTheory.ConvolutionTheory.L1.lactGen F E σ m D n τ k hk φ β hs ht a b Complex.I)
    intro u
    refine HarishChandra.U.induction halg ?_ hmul hadd u
    intro x
    rw [HarishChandra.ι_eq_sum_e]
    refine Finset.sum_induction _ (fun v => ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
      IsTens D (Function.update φ k (lact (jF v) (φ k))) (lact (jE v) β)) hadd ?_ ?_
    · simpa using halg 0
    · intro p _
      rw [Algebra.smul_def]
      exact hmul _ _ (halg _) (hgen p)
  rw [UpperTheory.ConvolutionTheory.L1.zc_eq hjE uE i, UpperTheory.ConvolutionTheory.L1.zc_eq hjF uF i]
  exact key _ φ₀ β₀ hs₀ ht₀
