import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace plainPolynomialPairNumber

open plainPairNumber (term rename_divDiff_eq_sum)

theorem rename_divDiff_add {r : ℕ} (l : Fin r) (A B : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l (A + B)) =
      rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l A) +
        rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l B) := by
  classical
  rw [rename_divDiff_eq_sum l (A + B) support_add,
    rename_divDiff_eq_sum l A Finset.subset_union_left,
    rename_divDiff_eq_sum l B Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_add, map_add, add_mul]

theorem term_tail {N q : ℕ} (i : Fin N) (μ : Fin N →₀ ℕ) (t : Fin q →₀ ℕ) (ν : Fin (N + q) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd q j) = μ j) (hn : ∀ j, ν (Fin.natAdd N j) = t j) :
    term (Fin.castAdd q i) ν =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q)) (term i μ) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  have hlt : ∀ j : Fin q, ¬ Fin.natAdd N j < Fin.castAdd q i := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hgt : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd N j := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hcc : ∀ j k : Fin N, (Fin.castAdd q j < Fin.castAdd q k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.castAdd q i),
      (X (Sum.inr j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => j < i), X (Sum.inr (Fin.castAdd q j)) ^ μ j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_false, Finset.prod_const_one, mul_one, hcc, hc]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.castAdd q i < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      (∏ j ∈ Finset.univ.filter (fun j => i < j), X (Sum.inl (Fin.castAdd q j)) ^ μ j) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_true, hcc, hc, hn]
  unfold term
  rw [h1, h3, hc i]
  simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem rename_monomial_tail {N q : ℕ} (t : Fin q →₀ ℕ) (c : ℤ) :
    rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) (monomial t c) =
      C c * ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, rename_X, rename_C]

theorem rename_divDiff_castAdd_monomial {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (t : Fin q →₀ ℕ) (c : ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) (monomial t c))) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q)))
          (monomial t c) := by
  classical
  set T : Fin (N + q) →₀ ℕ := t.mapDomain (Fin.natAdd N) with hT
  have hinj : Function.Injective
      (fun μ : Fin N →₀ ℕ => Finsupp.mapDomain (Fin.castAdd q) μ + T) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.castAdd_injective _ _) (add_right_cancel h)
  have hsub : (rename (Fin.castAdd q) G * monomial T c).support ⊆
      G.support.image (fun μ => Finsupp.mapDomain (Fin.castAdd q) μ + T) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · have hmem : ν - T ∈ (rename (Fin.castAdd q) G).support :=
        mem_support_iff.mpr (left_ne_zero_of_mul hν)
      rw [support_rename_of_injective (Fin.castAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hν
  rw [rename_monomial, ← hT, rename_divDiff_eq_sum (Fin.castAdd q i) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum i G subset_rfl, map_sum,
    Finset.sum_mul, rename_monomial_tail]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.castAdd q j) = μ j := by
    intro j
    have hj : Fin.castAdd q j ∉ Set.range (Fin.natAdd N : Fin q → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Fin.castAdd_injective _ _), hT,
      Finsupp.mapDomain_of_notMem_range _ _ hj, add_zero]
  have hn : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.natAdd N j) = t j := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd q : Fin N → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, hT,
      Finsupp.mapDomain_apply (Fin.natAdd_injective _ _), zero_add]
  rw [coeff_mul_monomial, coeff_rename_mapDomain _ (Fin.castAdd_injective _ _),
    term_tail i μ t _ hc hn, C_mul]
  simp only [map_mul, rename_C]
  ring

theorem rename_divDiff_castAdd_mul {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin q) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q)) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial t c => exact rename_divDiff_castAdd_monomial i G t c
  | add A B hA hB => rw [map_add, mul_add, rename_divDiff_add, hA, hB, map_add, mul_add]

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_mul_tail {σ : Type*} [DecidableEq σ] {q : ℕ} (cls : σ → K → ℤ)
    (L : Fin q → K → ℤ) (z : Fin q → σ) (hz : cls ∘ z = L) (A : MvPolynomial σ ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum cls (A * rename z Q) [] W = ∑ μ ∈ Q.support, Q.coeff μ * classNum cls A (classList L μ) W := by
  have hadd : ∀ H : MvPolynomial σ ℤ, classNum cls H [] W = classNumAddHom cls [] W H := fun _ => rfl
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Finset.mul_sum, hadd, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [rename_monomial, show monomial (μ.mapDomain z) (Q.coeff μ) =
      Q.coeff μ • monomial (μ.mapDomain z) (1 : ℤ) by rw [smul_monomial, smul_eq_mul, mul_one],
    mul_smul_comm, map_zsmul, smul_eq_mul, ← hadd, plainPairNumber.classNum_mul_monomial,
    classList_mapDomain, hz, List.append_nil]

theorem proof : plainPolynomialPairNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x x' f g m G hG hm q L Q hQ
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous (d + 1) := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show m + (d + 1 - m) = d + 1 by omega] at h3
  rw [BundleExamples.pairNum_eq P d _ _ _ _ hH]
  unfold pairNum
  have hr : ratDiv P 1 1 = fun _ => 0 := funext fun W => sub_self _
  have hz : ∀ n : Ideal (MRing ι O) → ℤ, cycEval n (fun _ => 0) = 0 := by
    intro n
    simp [cycEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hr, hz, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hZ := ratDiv_finite_support P (f i) (g i)
  simp only [cycEval_eq_sum hZ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hcls : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      Sum.map (Fin.castAdd q) (Fin.castAdd q) = Sum.elim x x' := by
    funext p
    cases p <;> simp [Fin.append_left]
  have hL : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) = L := by
    funext j
    simp [Fin.append_right]
  rw [rename_divDiff_castAdd_mul, classNum_mul_tail _ L _ hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [plainPairNumber.classNum_rename _ (Sum.map_injective.mpr
      ⟨Fin.castAdd_injective _ _, Fin.castAdd_injective _ _⟩), hcls]
  ring

end plainPolynomialPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
