import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

namespace FibreBound

theorem eval_pullback (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [pullback]
    · intro i; simp [pullback, linPoly, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f P) h

theorem exists_linear_injOn (T : Finset (Fin n → ℂ)) :
    ∃ c : Fin n → ℂ, Set.InjOn (fun x : Fin n → ℂ => ∑ j, c j * x j) T := by
  classical
  let p : (Fin n → ℂ) → (Fin n → ℂ) → Polynomial ℂ := fun x x' =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j - x' j)
  have hp : ∀ x x', x ≠ x' → p x x' ≠ 0 := by
    intro x x' hne h
    apply hne
    funext j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ x x' (t : ℂ), (p x x').eval t = ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) := by
    intro x x' t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (((T ×ˢ T).filter (fun z => z.1 ≠ z.2)).biUnion (fun z => (p z.1 z.2).roots.toFinset))
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  intro x hx x' hx' hxx'
  by_contra hne
  apply ht
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
  refine ⟨(x, x'), ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hx'⟩, hne⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp x x' hne), Polynomial.IsRoot, hev]
  have hs : ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) =
      (∑ j : Fin n, t ^ (j : ℕ) * x j) - ∑ j : Fin n, t ^ (j : ℕ) * x' j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; exact sub_eq_zero.mpr hxx'

theorem exists_monic_aeval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (s : MvPolynomial (Fin n) ℂ ⧸ J) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ),
      g.Monic ∧ g.natDegree ≤ projDegree J A ∧ Polynomial.aeval s g = 0 := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s
  have : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := TensorProduct.isScalarTower_left
  have : Module.Free (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := Module.Free.of_divisionRing _ _
  let t : TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.TensorProduct.includeRight s
  have hq : minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t ∣
      f.map (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hf,
      map_zero]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (MvPolynomial (Fin d) ℂ)) hfm hq
  have hqm : (minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t).Monic :=
    minpoly.monic (IsIntegral.of_finite _ t)
  rw [hqm.leadingCoeff, Polynomial.C_1, mul_one] at hg
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) :=
    IsFractionRing.injective _ _
  refine ⟨g, Polynomial.monic_of_injective hinj (hg ▸ hqm), ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hg]
    exact minpoly.natDegree_le t
  · have h1 : TensorProduct.mk (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J) 1 (Polynomial.aeval s g) = 0 := by
      rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply,
        ← Polynomial.aeval_algHom_apply,
        ← Polynomial.aeval_map_algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)), hg]
      exact minpoly.aeval _ t
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (MvPolynomial (Fin d) ℂ))
      (TensorProduct.mk _ (FractionRing (MvPolynomial (Fin d) ℂ)) _ 1)).mp h1
    rw [Submonoid.smul_def, Algebra.smul_def] at hc
    refine (mul_eq_zero.mp hc).resolve_left ?_
    intro h0
    apply nonZeroDivisors.coe_ne_zero c
    apply hA.injective
    rw [map_zero]
    exact h0

theorem proof : FibreBound.Statement := by
  intro n d J A hJ _ hA y
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  have hbound : ∀ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ fibre J A y →
      T.card ≤ projDegree J A := by
    intro T hT
    obtain ⟨c, hc⟩ := exists_linear_injOn T
    obtain ⟨g, hgm, hgd, hg⟩ :=
      exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (∑ j, C (c j) * X j))
    have hgy : (g.map (MvPolynomial.eval y)).Monic := hgm.map _
    have hroot : ∀ x ∈ T, (∑ j, c j * x j) ∈ (g.map (MvPolynomial.eval y)).roots.toFinset := by
      intro x hx
      obtain ⟨hxJ, hxA⟩ := hT (Finset.mem_coe.mpr hx)
      let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ :=
        Ideal.Quotient.lift J (eval x) (fun q hq => hxJ q hq)
      have hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) =
          MvPolynomial.eval y := by
        refine RingHom.ext fun P => ?_
        change ev (Ideal.Quotient.mk J (pullback A P)) = _
        rw [Ideal.Quotient.lift_mk, eval_pullback, hxA]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgy.ne_zero, Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have h := congrArg ev hg
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hev, map_zero] at h
      have hs : ev (Ideal.Quotient.mk J (∑ j, C (c j) * X j)) = ∑ j, c j * x j := by
        change eval x (∑ j, C (c j) * X j) = _
        simp
      rw [hs] at h
      exact h
    calc T.card = (T.image fun x => ∑ j, c j * x j).card := (Finset.card_image_of_injOn hc).symm
      _ ≤ (g.map (MvPolynomial.eval y)).roots.toFinset.card := Finset.card_le_card (by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
          exact hroot x hx)
      _ ≤ Multiset.card (g.map (MvPolynomial.eval y)).roots := Multiset.toFinset_card_le _
      _ ≤ (g.map (MvPolynomial.eval y)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := hgm.natDegree_map _
      _ ≤ projDegree J A := hgd
  have hne : (fibre J A y).Nonempty := by
    have hmax : (RingHom.ker (MvPolynomial.eval y)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, eval_C _⟩)
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (MvPolynomial.eval y)) (by
        intro P hP
        have hP0 : P = 0 := hA.injective (by rw [map_zero]; exact hP)
        rw [hP0]; exact Ideal.zero_mem _)
    have := hQ
    have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hQ'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    refine ⟨x, fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact Q.zero_mem), ?_⟩
    funext i
    have h1 : X i - C (y i) ∈ RingHom.ker (MvPolynomial.eval y) := by simp [RingHom.mem_ker]
    rw [← hQc] at h1
    have h2 := hmem (pullback A (X i - C (y i))) h1
    rw [eval_pullback] at h2
    simpa [sub_eq_zero] using h2
  have hfin : (fibre J A y).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (projDegree J A + 1)
    have := hbound T hT
    omega
  refine ⟨hne, hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ (by simp)

end FibreBound

end

end GroundTheory.Heights₂.Heights.ComplexSets
