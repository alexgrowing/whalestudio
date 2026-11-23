import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section IntegralMvPolynomialLemmas
variable {L V σ : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
  [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]

variable [LinearOrder σ]

end IntegralMvPolynomialLemmas

end UpperTheory.Gal.productCup_of_system

private theorem lG_of_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ e : B →ₐ[ℂ] ℂ, ∀ b ∈ I, e b = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ M)
  haveI : Algebra.IsIntegral ℂ (B ⧸ M) := Algebra.IsIntegral.of_finite ℂ _
  have hbij : Function.Bijective (algebraMap ℂ (B ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ M)) hbij
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), fun b hb => ?_⟩
  have h0 : Ideal.Quotient.mk M b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hb)
  simp [h0]

private theorem lG_of_lemma_2 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W] (N : Submodule ℂ W)
    (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (e : B →ₐ[ℂ] ℂ) :
    ∃ S : Submodule ℂ W, (∀ x ∈ S, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) ∧
      ∀ x, (∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) → x ∈ S := by
  refine ⟨{ carrier := {x | ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N}
            add_mem' := ?_
            zero_mem' := ⟨1, by simp, by simp⟩
            smul_mem' := ?_ }, fun x hx => hx, fun x hx => hx⟩
  · rintro x y ⟨b1, h1, hx⟩ ⟨b2, h2, hy⟩
    refine ⟨b1 * b2, by simp [h1, h2], ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [Subalgebra.coe_mul, mul_comm (b1 : L), mul_smul]
      exact hN b2 _ hx
    · rw [Subalgebra.coe_mul, mul_smul]
      exact hN b1 _ hy
  · rintro c x ⟨b, hb, hx⟩
    exact ⟨b, hb, by rw [smul_comm]; exact N.smul_mem c hx⟩

private theorem lG_of_lemma_3 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W]
    (N : Submodule ℂ W) (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (x : W)
    (hx : ∀ e : B →ₐ[ℂ] ℂ, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) : x ∈ N := by
  let I : Ideal B :=
    { carrier := {b | (b : L) • x ∈ N}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact N.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact hN c _ hb }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := by rw [hI]; exact Submodule.mem_top
    change ((1 : B) : L) • x ∈ N at h1
    simpa using h1
  · obtain ⟨e, he⟩ := lG_of_lemma B I hI
    obtain ⟨b, hb, hbx⟩ := hx e
    exact absurd (he b hbx) hb

theorem UpperTheory.Gal.productCup_of_system.lG_of :
    LG := by
  intro L _ _ B _ V σ _ _ _ _ _ _ A w hA
  have hAs : ∀ s, ∀ b : B, ∀ v ∈ A s, (b : L) • v ∈ A s := fun s b v hv => by
    simpa using hA s (b : L) b.2 v hv
  have hloc : ∀ (e : B →ₐ[ℂ] ℂ) (N : Submodule ℂ V), (∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) →
      ∀ v ∈ locM B e N, ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ N := by
    intro e N hN v hv
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B N hN e
    have hle : locM B e N ≤ S := by
      unfold locM
      rw [Submodule.span_le]
      intro u hu
      exact hS2 u hu
    exact hS1 v (hle hv)
  constructor
  · intro n c hc
    have hwd : ∀ (b : L) (x : Finset σ → V),
        wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) (b • x) =
          b • wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x := by
      intro b x
      funext t
      simp [wd, Finset.smul_sum, smul_comm b]
    have hC : ∀ (A' : Finset σ → Submodule ℂ V) (x : Finset σ → V),
        x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) ↔
          ∀ s, x s ∈ (if (s.card : ℤ) = n - 1 then A' s else ⊥) := by
      intro A' x
      simp [acx, Submodule.mem_pi]
    have hB : ∀ (A' : Finset σ → Submodule ℂ V) (c : Finset σ → V),
        c ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).B n ↔
          ∃ x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
            wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x = c := by
      intro A' c
      simp [Cx.B, acx]
    have hCstab : ∀ b : B, ∀ x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
        (b : L) • x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) := by
      intro b x hx
      rw [hC] at hx ⊢
      intro s
      have hxs := hx s
      simp only [Pi.smul_apply]
      split_ifs at hxs ⊢ with h
      · exact hAs s b _ hxs
      · rw [Submodule.mem_bot] at hxs ⊢
        simp [hxs]
    have hNstab : ∀ b : B, ∀ c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n,
        (b : L) • c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n := by
      intro b c hc
      rw [hB] at hc ⊢
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨_, hCstab b x hx, hwd _ _⟩
    refine lG_of_lemma_3 B _ hNstab c fun e => ?_
    obtain ⟨x, hx, rfl⟩ := (hB _ _).1 (hc e)
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hCstab e
    have hxS : x ∈ S := by
      rw [← Finset.univ_sum_single x]
      refine S.sum_mem fun s _ => ?_
      have hxs := (hC _ x).1 hx s
      split_ifs at hxs with h
      · obtain ⟨b, hb, hbv⟩ := hloc e (A s) (hAs s) _ hxs
        apply hS2
        refine ⟨b, hb, ?_⟩
        rw [hC]
        intro t
        by_cases hts : t = s
        · subst hts
          simpa [h] using hbv
        · simp [hts]
      · rw [Submodule.mem_bot] at hxs
        rw [hxs, Pi.single_zero]
        exact S.zero_mem
    obtain ⟨b, hb, hbx⟩ := hS1 x hxS
    exact ⟨b, hb, (hB _ _).2 ⟨_, hbx, hwd _ _⟩⟩
  · intro m hm
    have hmem : ∀ r ∈ Set.range w, ∀ u ∈ A ∅,
        r • u ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro r hr u hu
      unfold sm
      exact (le_iSup₂ (f := fun r (_ : r ∈ Set.range w) =>
        Submodule.map (Algebra.lsmul ℂ ℂ V r) (A ∅)) r hr) (Submodule.mem_map_of_mem hu)
    have hstab : ∀ b : B, ∀ v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w),
        (b : L) • v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro b v hv
      have hle : sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) ≤
          (sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w)).comap (Algebra.lsmul ℂ ℂ V (b : L)) := by
        conv_lhs => unfold sm
        refine iSup₂_le fun r hr => ?_
        rintro _ ⟨u, hu, rfl⟩
        rw [Submodule.mem_comap]
        simp only [Algebra.lsmul_coe]
        rw [smul_comm]
        exact hmem r hr _ (hAs ∅ b u hu)
      simpa using hle hv
    refine lG_of_lemma_3 B _ hstab m fun e => ?_
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hstab e
    apply hS1
    have hle : sm (Algebra.lsmul ℂ ℂ V) (locM B e (A ∅)) (Set.range w) ≤ S := by
      conv_lhs => unfold sm
      refine iSup₂_le fun r hr => ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨b, hb, hbv⟩ := hloc e (A ∅) (hAs ∅) v hv
      apply hS2
      refine ⟨b, hb, ?_⟩
      simp only [Algebra.lsmul_coe]
      rw [smul_comm]
      exact hmem r hr _ hbv
    exact hle (hm e)
