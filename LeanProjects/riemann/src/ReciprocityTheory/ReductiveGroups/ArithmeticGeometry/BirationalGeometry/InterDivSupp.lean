import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppA
import Lemmata.GeneralBFactTerForm.Imports

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Dim

variable {σ : Type*} [Finite σ]

theorem dim_quot_minimal_add_one (P W : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (s : MvPolynomial σ ℤ) (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hq : W.map (Ideal.Quotient.mk P) ∈
      (Ideal.span {Ideal.Quotient.mk P s}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P s} = (Ideal.span {s}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P s}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk P)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk P s ∈ W.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hsW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hs this
  have key := mvPolynomialInt_dimFormula P W hPW
  rw [hh] at key
  exact_mod_cast key

theorem withBot_eq_of_add_one {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by
  first | exact Bl.general_b_fact_ter_form.goal1 .. | (apply Bl.general_b_fact_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_ter_form.goal1 <;> assumption)

end Dim

section Blocks

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def blockWeight [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0

theorem weight_blockWeight [DecidableEq K] (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro b _ hb
    simp [blockWeight, hb]
  · simp

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRing ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (blockWeight (ι := ι) k) s (a k) := by
  intro d hd
  rw [weight_blockWeight]
  exact h d (mem_support_iff.mpr hd) k

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal [DecidableEq K] {P : Ideal (MRing ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_of_isMultiHomog ha k)⟩

theorem isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A)
    [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜) (hW : W ∈ I.minimalPrimes) :
    W.IsHomogeneous 𝒜 := by
  have hWp : W.IsPrime := hW.1.1
  have h1 : (W.homogeneousCore 𝒜).toIdeal.IsPrime := hWp.homogeneousCore
  have h2 : I ≤ (W.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have h3 := hW.2 ⟨h1, h2⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  have e : (W.homogeneousCore 𝒜).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) h3
  exact e ▸ (W.homogeneousCore 𝒜).isHomogeneous

theorem exists_blockComponent [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRing ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, coeff m g = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then coeff m f else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (blockWeight k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem ℤ (blockWeight k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_blockWeight, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]

theorem isMultiHomogIdeal_of_isHomogeneous [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k))) :
    IsMultiHomogIdeal W := by
  refine ⟨{f | f ∈ W ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2, le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr fun f hf => hf.1)⟩
  choose g hgW hg using fun a : K → ℕ => exists_blockComponent hW a Finset.univ hf
  have hsum : f = ∑ a ∈ f.support.image (fun m k => ∑ i, m ⟨k, i⟩), g a := by
    ext m
    rw [coeff_sum]
    have e : ∀ a : K → ℕ,
        coeff m (g a) = if (fun k => ∑ i, m ⟨k, i⟩) = a then coeff m f else 0 := by
      intro a
      rw [hg a]
      by_cases h : (fun k => ∑ i, m ⟨k, i⟩) = a
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (funext fun k => h' k (Finset.mem_univ k))
    simp_rw [e]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
  rw [hsum]
  refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨hgW a, a, fun m hm k => ?_⟩
  rw [mem_support_iff, hg a] at hm
  by_contra hk
  exact hm (if_neg fun h => hk (h k (Finset.mem_univ k)))

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P W : Ideal (MRing ι)} {s : MRing ι} {a : K → ℕ}
    (hP : IsMultiHomogIdeal P) (hs : IsMultiHomog s a)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) : IsMultiHomogIdeal W := by
  classical
  refine isMultiHomogIdeal_of_isHomogeneous fun k => isHomogeneous_of_mem_minimalPrimes _
    ((isHomogeneous_of_isMultiHomogIdeal hP k).sup (Ideal.homogeneous_span _ _ ?_)) hW
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_of_isMultiHomog hs k)⟩

theorem charOf_prime {W : Ideal (MRing ι)} (hW : W.IsPrime) (hv : ¬ IsHorizontal W) :
    (charOf W).Prime := by
  have := hW
  have hJ : (W.comap (C : ℤ →+* MRing ι)).IsPrime := inferInstance
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ≠ 0 := fun h0 =>
    hv ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h0)
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime, ← Ideal.span_singleton_prime hg,
    Ideal.span_singleton_generator]
  exact hJ

end Blocks

theorem divSuppArith : DivSuppArithStatement := by
  intro K _ ι _ P n A s W hP hs hW
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  exact ⟨fun hh => ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩,
    fun hv => ⟨⟨hWp, hWmh, hWrel⟩, charOf_prime hWp hv, hdim⟩⟩

end ReciprocityTheory.ChartRestriction.G.Geo
