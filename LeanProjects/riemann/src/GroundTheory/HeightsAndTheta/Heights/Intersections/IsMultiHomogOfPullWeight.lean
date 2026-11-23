import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogGrad
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PullbackElimination

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_coordProd_mul {F : Type} [Field F] [Algebra ℤ F] {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (c : ∀ k, ι k) (y : (Σ k, ι k) → F) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y g = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (fun p => y p / y ⟨p.1, c p.1⟩) g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hprod : ∏ p : Σ k, ι k, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  have key : ∏ p : Σ k, ι k, y p ^ m p =
      (∏ k, y ⟨k, c k⟩ ^ d k) * ∏ p : Σ k, ι k, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [← hprod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow, mul_div_cancel₀ _ (hy p.1)]
  rw [key]
  ring

abbrev pullWeight {K' : Type} {ι' : K' → Type} (v : (Σ k, ι k) → (Σ k', ι' k')) : (Σ k, ι k) → (K' → ℕ) :=
  fun p => LocRingPow.multiDegWeight ι' (v p)

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isMultiHomog_of_pullWeight {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {D : K' → ℕ} (hf : IsWeightedHomogeneous (pullWeight v) f D) :
    IsMultiHomog f (fun k => D (κ k)) := by
  classical
  intro m hm k
  show ∑ i, m ⟨k, i⟩ = D (κ k)
  have h := hf (mem_support_iff.mp hm)
  have hw : ∀ p : Σ k, ι k, pullWeight v p (κ k) = LocRingPow.multiDegWeight ι p k := by
    intro p
    simp only [pullWeight, LocRingPow.multiDegWeight, hv.2.2.1 p, hv.1.eq_iff]
  have e1 := congrFun (LocRingPow.weight_multiDegWeight (ι := ι) m) k
  rw [← e1, ← congrFun h (κ k), Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, hw]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem rename_component (v : (Σ k, ι k) → (Σ k', ι' k')) (D : K' → ℕ) (f : MRing ι) :
    rename v (weightedHomogeneousComponent (pullWeight v) D f) =
      weightedHomogeneousComponent (LocRingPow.multiDegWeight ι') D (rename v f) := by
  rw [rename_eq_aeval]
  exact IndefiniteRowSideFullHecke.Inter.aeval_weightedHomogeneousComponent_of_weights _ _ _
    (fun p => isWeightedHomogeneous_X _ _ _) D f

end Homog

section Elim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem exists_elim {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {n : ℕ}
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) (hQ : IsArithVar (imageZ v P') (n + 1))
    {g : MRing ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) (hgP : g ∉ P')
    (c : ∀ k', ι' k') (hc : ∀ k', (X ⟨k', c k'⟩ : MRing ι') ∉ P') :
    ∃ (r : ℕ) (a : ℕ → MRing ι), a 0 ∉ imageZ v P' ∧
      ∑ i ∈ Finset.range (r + 1),
        rename v (a i) * (g ^ i * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') ^ (r - i)) ∈ P' := by
  classical
  have : P'.IsPrime := hP'.2.1.1
  have hQp : (imageZ v P').IsPrime := Ideal.IsPrime.comap _
  let ιB : MRing ι' →+* FractionRing (MRing ι' ⧸ P') :=
    (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (Ideal.Quotient.mk P')
  have hιB : ∀ f, ιB f = 0 ↔ f ∈ P' := fun f => by
    simp only [ιB, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))),
      Ideal.Quotient.eq_zero_iff_mem]
  let φA : MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ P') :=
    Ideal.Quotient.lift (imageZ v P') (ιB.comp (rename v).toRingHom) (fun f hf => (hιB _).mpr hf)
  have hφA : ∀ f, φA (Ideal.Quotient.mk _ f) = ιB (rename v f) := fun f => rfl
  let _ : Algebra (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι' ⧸ P')) := φA.toAlgebra
  have halg : ∀ f, algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk _ f) = ιB (rename v f) := fun f => rfl
  let y' : (Σ k', ι' k') → FractionRing (MRing ι' ⧸ P') := fun p => ιB (X p)
  have haeval : ∀ f : MRing ι', aeval y' f = ιB f := fun f => by
    have e : (aeval y' : MRing ι' →ₐ[ℤ] _).toRingHom = ιB :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun p => by simp [y'])
    exact congrArg (fun φ : MRing ι' →+* _ => φ f) e
  have hyc : ∀ k', y' ⟨k', c k'⟩ ≠ 0 := fun k' h => hc k' ((hιB _).mp h)

  have hρ : ∀ q : Σ k', ι' k', IsAlgebraic (MRing ι ⧸ imageZ v P') (y' q / y' ⟨q.1, c q.1⟩) := by
    intro q
    obtain ⟨m, Aj, a, -, hlead, hrel⟩ :=
      BlockRatioAlg.proof K ι K' ι' κ v P' n hv hP' hQ q ⟨q.1, c q.1⟩ rfl (hc q.1)
    refine ⟨∑ j : Fin (m + 1), Polynomial.monomial (j : ℕ) (Ideal.Quotient.mk (imageZ v P') (Aj j)), ?_, ?_⟩
    · intro h0
      have hcoeff : (∑ j : Fin (m + 1), Polynomial.monomial (j : ℕ)
          (Ideal.Quotient.mk (imageZ v P') (Aj j))).coeff m = Ideal.Quotient.mk _ (Aj (Fin.last m)) := by
        rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (Fin.last m)]
        · simp
        · intro j _ hj
          rw [Polynomial.coeff_monomial, if_neg]
          intro h
          exact hj (Fin.ext (by simpa using h))
        · simp
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact hlead (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff.symm)
    · have h := (hιB _).mpr hrel
      simp only [map_sum, map_mul, map_pow] at h
      have hne := pow_ne_zero m (hyc q.1)
      apply (mul_left_inj' hne).mp
      rw [zero_mul, map_sum, Finset.sum_mul, ← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.2
      rw [Polynomial.aeval_monomial, halg]
      have e : (y' q / y' ⟨q.1, c q.1⟩) ^ (j : ℕ) * y' ⟨q.1, c q.1⟩ ^ (j : ℕ) = y' q ^ (j : ℕ) := by
        rw [← mul_pow, div_mul_cancel₀ _ (hyc q.1)]
      rw [← pow_sub_mul_pow (y' ⟨q.1, c q.1⟩) hj]
      change _ = ιB (rename v (Aj j)) * y' q ^ (j : ℕ) * y' ⟨q.1, c q.1⟩ ^ (m - j : ℕ)
      linear_combination (ιB (rename v (Aj j)) * y' ⟨q.1, c q.1⟩ ^ (m - j : ℕ)) * e

  have hγ : IsAlgebraic (MRing ι ⧸ imageZ v P') (aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g) := by
    have : ∀ f : MRing ι', aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) f ∈
        Subalgebra.algebraicClosure (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι' ⧸ P')) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a =>
        rw [aeval_C]
        have e : algebraMap ℤ (FractionRing (MRing ι' ⧸ P')) a =
            algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι' ⧸ P')) (a : MRing ι ⧸ imageZ v P') := by
          simp
        rw [e]
        exact Subalgebra.algebraMap_mem _ _
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (hρ i)
    exact this g
  have hT := aeval_eq_coordProd_mul hg c y' hyc
  have hTne : (∏ k', y' ⟨k', c k'⟩ ^ d k') ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hyc k')
  have hγne : aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g ≠ 0 := by
    intro h
    apply hgP
    rw [← hιB, ← haeval, hT, h, mul_zero]
  obtain ⟨q, hq0, hq⟩ := hγ.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hγne)
  obtain ⟨q₀, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (imageZ v P')) Ideal.Quotient.mk_surjective q
  refine ⟨q₀.natDegree, fun i => q₀.coeff i, ?_, ?_⟩
  · intro h
    apply hq0
    rw [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem.mpr h]
  · have hsum : ∑ i ∈ Finset.range (q₀.natDegree + 1),
        ιB (rename v (q₀.coeff i)) * aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g ^ i = 0 := by
      rw [← hq, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le (Polynomial.natDegree_map_le))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.coeff_map, Algebra.smul_def, halg]
    have hιT : ιB (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') = ∏ k', y' ⟨k', c k'⟩ ^ d k' := by
      simp only [map_prod, map_pow, y']
    rw [← hιB, map_sum]
    calc ∑ i ∈ Finset.range (q₀.natDegree + 1),
          ιB (rename v (q₀.coeff i) * (g ^ i * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') ^ (q₀.natDegree - i)))
        = ∑ i ∈ Finset.range (q₀.natDegree + 1), (∏ k', y' ⟨k', c k'⟩ ^ d k') ^ q₀.natDegree *
            (ιB (rename v (q₀.coeff i)) * aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g ^ i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : i ≤ q₀.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [map_mul, map_mul, map_pow, map_pow, ← haeval g, hT, hιT, mul_pow,
            ← pow_sub_mul_pow (∏ k', y' ⟨k', c k'⟩ ^ d k') hi']
          ring
      _ = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]

theorem exists_elim_homog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {n : ℕ}
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) (hQ : IsArithVar (imageZ v P') (n + 1))
    {g : MRing ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) (hgP : g ∉ P')
    (c : ∀ k', ι' k') (hc : ∀ k', (X ⟨k', c k'⟩ : MRing ι') ∉ P') :
    ∃ (r : ℕ) (a : ℕ → MRing ι) (D : K' → ℕ), a 0 ∉ imageZ v P' ∧
      IsWeightedHomogeneous (pullWeight v) (a 0) D ∧
      ∑ i ∈ Finset.range (r + 1),
        rename v (a i) * (g ^ i * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') ^ (r - i)) ∈ P' := by
  classical
  obtain ⟨r, a, ha0, hE⟩ := exists_elim hv hP' hQ hg hgP c hc
  obtain ⟨D, hD⟩ : ∃ D, weightedHomogeneousComponent (pullWeight v) D (a 0) ∉ imageZ v P' := by
    by_contra h
    push_neg at h
    apply ha0
    rw [← sum_weightedHomogeneousComponent (w := pullWeight v) (φ := a 0),
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp _)]
    exact Ideal.sum_mem _ fun D _ => h D
  refine ⟨r, fun i => weightedHomogeneousComponent (pullWeight v) D (a i), D, hD,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  have hmem := LocRingPow.component_mem hP'.2.1.2.1 hE (D + r • d)
  convert hmem using 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hgi : IsWeightedHomogeneous (LocRingPow.multiDegWeight ι')
      (g ^ i * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') ^ (r - i)) (r • d) := by
    have h1 := AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_pow hg i)
      (AvoidRing.isMultiHomog_pow (AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι') c d) (r - i))
    rw [← add_smul, Nat.add_sub_cancel' hi'] at h1
    exact LocRingPow.isMultiHomog_iff.mp h1
  rw [LocRingPow.component_mul_right hgi, rename_component]

theorem eval_eq_zero {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {g : MRing ι'} {d : K' → ℕ}
    (c : ∀ k', ι' k') {r : ℕ} {a : ℕ → MRing ι}
    (hE : ∑ i ∈ Finset.range (r + 1),
        rename v (a i) * (g ^ i * (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k') ^ (r - i)) ∈ P')
    {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P') (hgz : eval z' (map (Int.castRingHom ℂ) g) = 0)
    (hz : ∀ k', z' ⟨k', c k'⟩ ≠ 0) :
    eval (fun p => z' (v p)) (map (Int.castRingHom ℂ) (a 0)) = 0 := by
  have h0 := hz'.2 _ hE
  rw [Finset.sum_range_succ'] at h0
  simp only [map_add, map_sum, map_mul, map_pow, hgz, ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mul, Nat.sub_zero] at h0
  have hT : eval z' (map (Int.castRingHom ℂ) (∏ k', (X ⟨k', c k'⟩ : MRing ι') ^ d k')) ≠ 0 := by
    rw [map_prod, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k' _ => by
      rw [map_pow, map_pow, map_X, eval_X]
      exact pow_ne_zero _ (hz k')
  rcases mul_eq_zero.mp h0 with h | h
  · rw [map_rename, eval_rename] at h
    exact h
  · exact absurd (pow_eq_zero_iff'.mp h).1 hT
end Elim

end PullbackElimination

open PullbackElimination in

theorem PullbackEliminationOfVariable.proof : PullbackEliminationOfVariable.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' J' n hv hP' hQ hJ hJP
  obtain ⟨S, hS, rfl⟩ := hJ
  obtain ⟨g, hgS, hgP⟩ : ∃ g ∈ S, g ∉ P' := by
    by_contra h
    push_neg at h
    exact hJP (Ideal.span_le.mpr h)
  obtain ⟨d, hg⟩ := hS g hgS
  have : P'.IsPrime := hP'.2.1.1
  have hQp : (imageZ v P').IsPrime := Ideal.IsPrime.comap _
  have key : ∀ c : (∀ k', ι' k'), (∀ k', (X ⟨k', c k'⟩ : MRing ι') ∉ P') →
      ∃ (h : MRing ι) (a : K → ℕ), IsMultiHomog h a ∧ h ∉ imageZ v P' ∧
        ∀ z' ∈ mcPts P', eval z' (map (Int.castRingHom ℂ) g) = 0 → (∀ k', z' ⟨k', c k'⟩ ≠ 0) →
          eval (fun p => z' (v p)) (map (Int.castRingHom ℂ) h) = 0 := by
    intro c hc
    obtain ⟨r, a, D, ha0, hhom, hE⟩ := exists_elim_homog hv hP' hQ hg hgP c hc
    exact ⟨a 0, fun k => D (κ k), isMultiHomog_of_pullWeight hv hhom, ha0,
      fun z' hz' hgz hz => eval_eq_zero c hE hz' hgz hz⟩
  choose! hc ac hhom hnot hvan using key
  let good := Finset.univ.filter (fun c : (∀ k', ι' k') => ∀ k', (X ⟨k', c k'⟩ : MRing ι') ∉ P')
  refine ⟨∏ c ∈ good, hc c, ∑ c ∈ good, ac c,
    AvoidRing.isMultiHomog_prod _ _ _ fun c hcg => hhom c (Finset.mem_filter.mp hcg).2, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, hcg, hc'⟩ := (hQp.prod_mem_iff).mp hmem
    exact hnot c (Finset.mem_filter.mp hcg).2 hc'
  · intro z' hz' hzJ
    choose e he using hz'.1
    have hgood : ∀ k', (X ⟨k', e k'⟩ : MRing ι') ∉ P' := fun k' hX =>
      he k' (by simpa using hz'.2 _ hX)
    have h1 := hvan e hgood z' hz' (hzJ.2 g (Ideal.subset_span hgS)) he
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩) h1

end GroundTheory.Heights₂.Heights.Inter
