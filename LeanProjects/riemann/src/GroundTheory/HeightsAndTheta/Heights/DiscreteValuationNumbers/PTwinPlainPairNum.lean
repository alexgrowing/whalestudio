import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace plainPairNumber

section ClassNum

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_perm {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) {L₁ L₂ : List (K → ℤ)}
    (h : L₁.Perm L₂) (W : Ideal (MRing ι O)) : classNum cls H L₁ W = classNum cls H L₂ W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [FlagTypings.vNumL_perm W (h.append_left _)]

theorem classNum_rename {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 2
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_eq_sum_of_subset {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by
    rw [mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]

omit [DecidableEq K] in

theorem classList_add_perm {σ : Type*} (cls : σ → K → ℤ) (μ ν : σ →₀ ℕ) :
    (classList cls (μ + ν)).Perm (classList cls μ ++ classList cls ν) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [classList, Multiset.coe_toList, map_add, Multiset.map_add]

omit [DecidableEq K] in

theorem classList_sum_single {σ : Type*} (cls : σ → K → ℤ) {r : ℕ} (a : Fin r → σ) :
    (classList cls (∑ j, Finsupp.single (a j) 1)).Perm (List.ofFn fun j => cls (a j)) := by
  have hs : ∀ s : Multiset (Fin r), (s.map fun x => ({a x} : Multiset σ)).sum = s.map a := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons b s ih => simp [ih]
  rw [← Multiset.coe_eq_coe, classList, Multiset.coe_toList, map_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [Finset.sum_eq_multiset_sum, hs, Multiset.map_map, ← Fin.univ_val_map]
  rfl

theorem classNum_mul_monomial {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (A : MvPolynomial σ ℤ)
    (t : σ →₀ ℕ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (A * monomial t 1) Q W = classNum cls A (classList cls t ++ Q) W := by
  have hsub : (A * monomial t 1).support ⊆ A.support.image (· + t) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · rw [mul_one] at hν
      exact Finset.mem_image.mpr ⟨ν - t, mem_support_iff.mpr hν, tsub_add_cancel_of_le hle⟩
    · exact absurd rfl hν
  rw [classNum_eq_sum_of_subset cls _ Q W hsub,
    Finset.sum_image fun a _ b _ h => add_right_cancel h]
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_mul_monomial, mul_one, ← List.append_assoc,
    FlagTypings.vNumL_perm W ((classList_add_perm cls μ t).append_right Q)]

end ClassNum

section DivDiff

def term {r : ℕ} (l : Fin r) (μ : Fin r →₀ ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  (∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
    (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
    ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j

theorem rename_divDiff_eq_sum {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ)
    {S : Finset (Fin r →₀ ℕ)} (hS : G.support ⊆ S) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ S, C (G.coeff μ) * term l μ := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine (Finset.sum_subset hS ?_).trans (Finset.sum_congr rfl fun μ _ => ?_)
  · intro μ _ hμ
    rw [mem_support_iff, not_not] at hμ
    simp [hμ]
  · unfold term
    ring

def tailMono (N r : ℕ) : Fin (N + r) →₀ ℕ := ∑ j : Fin r, Finsupp.single (Fin.natAdd N j) 1

theorem tailMono_castAdd (N r : ℕ) (i : Fin N) : tailMono N r (Fin.castAdd r i) = 0 := by
  rw [tailMono, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

theorem tailMono_natAdd (N r : ℕ) (j : Fin r) : tailMono N r (Fin.natAdd N j) = 1 := by
  rw [tailMono, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    apply hb
    ext
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    omega
  · simp

theorem term_tail {N r : ℕ} (i : Fin N) (μ : Fin N →₀ ℕ) (ν : Fin (N + r) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd r j) = μ j) (hn : ∀ j, ν (Fin.natAdd N j) = 1) :
    term (Fin.castAdd r i) ν =
      rename (Sum.map (Fin.castAdd r) (Fin.castAdd r)) (term i μ) *
        ∏ j : Fin r, X (Sum.inl (Fin.natAdd N j)) := by
  have hlt : ∀ j : Fin r, ¬ Fin.natAdd N j < Fin.castAdd r i := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hgt : ∀ j : Fin r, Fin.castAdd r i < Fin.natAdd N j := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hcc : ∀ j k : Fin N, (Fin.castAdd r j < Fin.castAdd r k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.castAdd r i),
      (X (Sum.inr j) : MvPolynomial (Fin (N + r) ⊕ Fin (N + r)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => j < i), X (Sum.inr (Fin.castAdd r j)) ^ μ j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_false, Finset.prod_const_one, mul_one, hcc, hc]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.castAdd r i < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + r) ⊕ Fin (N + r)) ℤ) ^ ν j) =
      (∏ j ∈ Finset.univ.filter (fun j => i < j), X (Sum.inl (Fin.castAdd r j)) ^ μ j) *
        ∏ j : Fin r, X (Sum.inl (Fin.natAdd N j)) := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_true, hcc, hc, hn, pow_one]
  unfold term
  rw [h1, h3, hc i]
  simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem prod_X_natAdd (N r : ℕ) :
    rename (Fin.natAdd N) (∏ j : Fin r, (X j : MvPolynomial (Fin r) ℤ)) =
      monomial (tailMono N r) 1 := by
  rw [tailMono, monomial_sum_one, map_prod]
  simp only [rename_X]
  rfl

theorem rename_divDiff_castAdd {N r : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) (∏ j : Fin r, X j))) =
      rename (Sum.map (Fin.castAdd r) (Fin.castAdd r))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        ∏ j : Fin r, X (Sum.inl (Fin.natAdd N j)) := by
  classical
  have hinj : Function.Injective
      (fun μ : Fin N →₀ ℕ => Finsupp.mapDomain (Fin.castAdd r) μ + tailMono N r) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.castAdd_injective _ _) (add_right_cancel h)
  have hsub : (rename (Fin.castAdd r) G * monomial (tailMono N r) 1).support ⊆
      G.support.image (fun μ => Finsupp.mapDomain (Fin.castAdd r) μ + tailMono N r) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · rw [mul_one] at hν
      have hmem : ν - tailMono N r ∈ (rename (Fin.castAdd r) G).support := mem_support_iff.mpr hν
      rw [support_rename_of_injective (Fin.castAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hν
  rw [prod_X_natAdd, rename_divDiff_eq_sum (Fin.castAdd r i) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum i G subset_rfl, map_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (Finsupp.mapDomain (Fin.castAdd r) μ + tailMono N r) (Fin.castAdd r j) = μ j := by
    intro j
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Fin.castAdd_injective _ _), tailMono_castAdd,
      add_zero]
  have hn : ∀ j, (Finsupp.mapDomain (Fin.castAdd r) μ + tailMono N r) (Fin.natAdd N j) = 1 := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd r : Fin N → Fin (N + r)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, tailMono_natAdd, zero_add]
  rw [coeff_mul_monomial, coeff_rename_mapDomain _ (Fin.castAdd_injective _ _), mul_one,
    term_tail i μ _ hc hn, map_mul, rename_C, mul_assoc]

end DivDiff

theorem proof : plainPairNumber.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P d N x x' f g m G hG Q hQ
  have hH : (rename (Fin.castAdd Q.length) G * rename (Fin.natAdd N) (∏ j : Fin Q.length, X j) :
      MvPolynomial (Fin (N + Q.length)) ℤ).IsHomogeneous (d + 1) := by
    have h2 : (∏ j : Fin Q.length, (X j : MvPolynomial (Fin Q.length) ℤ)).IsHomogeneous
        Q.length := by
      simpa using IsHomogeneous.prod Finset.univ (fun j => (X j : MvPolynomial (Fin Q.length) ℤ))
        (fun _ => 1) fun j _ => isHomogeneous_X ℤ j
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd Q.length)).mul
      (h2.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show m + Q.length = d + 1 by omega] at h3
  rw [BundleExamples.pairNum_eq P d _ _ _ _ hH]
  unfold pairNum
  have hr : ratDiv P 1 1 = fun _ => 0 := funext fun W => sub_self _
  have hz : ∀ n : Ideal (MRing ι O) → ℤ, cycEval n (fun _ => 0) = 0 := by
    intro n
    simp [cycEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hr, hz, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext W
  have hm : (∏ j : Fin Q.length, (X (Sum.inl (Fin.natAdd N j)) :
      MvPolynomial (Fin (N + Q.length) ⊕ Fin (N + Q.length)) ℤ)) =
      monomial (∑ j : Fin Q.length, Finsupp.single (Sum.inl (Fin.natAdd N j)) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [rename_divDiff_castAdd, hm, classNum_mul_monomial, classNum_rename _ (Sum.map_injective.mpr
      ⟨Fin.castAdd_injective _ _, Fin.castAdd_injective _ _⟩)]
  have hcls : Sum.elim (Fin.append x Q.get) (Fin.append x' Q.get) ∘
      Sum.map (Fin.castAdd Q.length) (Fin.castAdd Q.length) = Sum.elim x x' := by
    funext p
    cases p <;> simp [Fin.append_left]
  rw [hcls]
  refine classNum_perm _ _ ?_ W
  rw [List.append_nil]
  refine (classList_sum_single _ _).trans (List.Perm.of_eq ?_)
  simp [Fin.append_right]

end plainPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
