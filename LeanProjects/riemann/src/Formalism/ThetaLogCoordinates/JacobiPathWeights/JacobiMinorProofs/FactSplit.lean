import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.IndexWeightsDominance

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace LowHighPartSplit

variable {n : ℕ}

def lowP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => x.1 < i

def highP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => ¬ x.1 < i

theorem low_add_high (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : lowP i e + highP i e = e := by
  ext x
  simp only [lowP, highP, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases h : x.1 < i <;> simp [h]

theorem lowerUnipotent_symm_apply (i : ℕ) (e : ℕ × Fin n →₀ ℕ) (j : ℕ) (a : Fin n) :
    lowP i e (j, a) = if j < i then e (j, a) else 0 := by
  simp [lowP, Finsupp.filter_apply]

theorem highPart_apply (i : ℕ) (e : ℕ × Fin n →₀ ℕ) (j : ℕ) (a : Fin n) :
    highP i e (j, a) = if j < i then 0 else e (j, a) := by
  simp only [highP, Finsupp.filter_apply]
  by_cases h : j < i <;> simp [h]

private theorem weight_indicator_eq_degree (d : ℕ × Fin n →₀ ℕ) (j : ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = j then 1 else 0) d = ∑ a, d (j, a) := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx _ y hy _ hxy
    rw [Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  · intro a _ ha
    exact ⟨(j, a), Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ha, rfl⟩, ha, rfl⟩
  · intro x hx _
    rw [Finset.mem_filter] at hx
    rw [← hx.2]

theorem mem_polB {R : Type*} [CommRing R] {N : ℕ} {B : ℕ → ℕ} {f : MvPolynomial (ℕ × Fin n) R} :
    f ∈ polB R n N B ↔ ∀ e ∈ f.support, ∀ j, ∑ a, e (j, a) = if j < N then B j else 0 := by
  simp only [polB, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous]
  constructor
  · intro h e he j
    have := h j (mem_support_iff.mp he)
    rw [weight_indicator_eq_degree] at this
    exact this
  · intro h j d hd
    rw [weight_indicator_eq_degree]
    exact h d (mem_support_iff.mpr hd) j

def Gc {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    MvPolynomial (ℕ × Fin n) k :=
  ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e) (coeff e G)

theorem decomp {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    G = ∑ β ∈ G.support.image (highP i), Gc i G β * monomial β 1 := by
  symm
  simp only [Gc, Finset.sum_mul, monomial_mul, mul_one]
  have h1 : ∀ β ∈ G.support.image (highP i),
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e + β) (coeff e G) =
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial e (coeff e G) :=
    fun β _ => Finset.sum_congr rfl fun e he => by rw [← (Finset.mem_filter.mp he).2, low_add_high]
  rw [Finset.sum_congr rfl h1, Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)]
  exact G.as_sum.symm

theorem supp_zero {σ L : Type*} [CommRing L] {Lo : Set σ} {P : MvPolynomial σ L} (hP : P ∈ supported L Lo)
    {e : σ →₀ ℕ} (he : e ∈ P.support) {x : σ} (hx : x ∉ Lo) : e x = 0 := by
  by_contra h
  apply hx
  exact (mem_supported.mp hP) (Finset.mem_coe.mpr ((mem_vars x).mpr ⟨e, he, Finsupp.mem_support_iff.mpr h⟩))

theorem coeff_key {σ τ L : Type*} [CommRing L] (Lo : Set σ) (T : Finset τ) (A : τ → MvPolynomial σ L)
    (m : τ → σ →₀ ℕ) (hA : ∀ β ∈ T, A β ∈ supported L Lo) (hm : ∀ β ∈ T, ∀ x ∈ Lo, m β x = 0)
    (hinj : ∀ β ∈ T, ∀ γ ∈ T, m β = m γ → β = γ) {β : τ} (hβ : β ∈ T) {e : σ →₀ ℕ} (he : e ∈ (A β).support) :
    e + m β ∈ (∑ γ ∈ T, A γ * monomial (m γ) 1).support := by
  rw [mem_support_iff, coeff_sum, Finset.sum_eq_single β]
  · rw [coeff_mul_monomial, mul_one]
    exact mem_support_iff.mp he
  · intro γ hγ hne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · rw [mul_one]
      by_contra hc
      have hf : e + m β - m γ ∈ (A γ).support := mem_support_iff.mpr hc
      apply hne
      apply hinj γ hγ β hβ
      ext x
      by_cases hx : x ∈ Lo
      · rw [hm β hβ x hx, hm γ hγ x hx]
      · have h1 := supp_zero (hA γ hγ) hf hx
        have h2 := supp_zero (hA β hβ) he hx
        have h3 := Finsupp.le_def.mp hle x
        rw [Finsupp.tsub_apply, Finsupp.add_apply, h2] at h1
        rw [Finsupp.add_apply, h2] at h3
        omega
    · rfl
  · intro h
    exact absurd hβ h

variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]

def Psi : MvPolynomial (ℕ × Fin n) k →+* MvPolynomial (LVar ℕ Empty n) (GenField k n) :=
  ((sharpHom isVec S (genMat k n)⁻¹ (genMat k n)).toRingHom.comp (map (genφ k n))).comp
    (rename (R := k) (Sum.inl : ℕ × Fin n → LVar ℕ Empty n)).toRingHom

theorem Psi_apply (G : MvPolynomial (ℕ × Fin n) k) : Psi isVec S G = genH isVec S (rename Sum.inl G) := rfl

def loSet (n : ℕ) (S : Set ℕ) : Set (LVar ℕ Empty n) := {x | ∃ j a, j ∈ S ∧ x = Sum.inl (j, a)}

theorem Psi_X_low {j : ℕ} (hj : j ∈ S) (a : Fin n) :
    Psi isVec S (X (j, a) : MvPolynomial (ℕ × Fin n) k) ∈ supported (GenField k n) (loSet n S) := by
  have hgen : ∀ Mt : Matrix (Fin n) (Fin n) (GenField k n),
      Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
        (Mt.map C) a ∈ supported (GenField k n) (loSet n S) := by
    intro Mt
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ⟨j, b, hj, rfl⟩)
      (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
  simp only [Psi_apply, genH, rename_X, map_X, sharpHom, aeval_X, if_pos hj]
  split_ifs
  · exact hgen _
  · rw [← Matrix.transpose_map]
    exact hgen _

theorem Psi_X_high {j : ℕ} (hj : j ∉ S) (a : Fin n) :
    Psi isVec S (X (j, a) : MvPolynomial (ℕ × Fin n) k) = X (Sum.inl (j, a)) := by
  simp only [Psi_apply, genH, rename_X, map_X, sharpHom, aeval_X, if_neg hj]

theorem Psi_C (c : k) : Psi (n := n) isVec S (C c) = C (genφ k n c) := by
  simp only [Psi_apply, genH, rename_C, map_C, sharpHom, aeval_C, algebraMap_eq]

theorem Psi_monomial (e : ℕ × Fin n →₀ ℕ) (c : k) :
    Psi isVec S (monomial e c) = C (genφ k n c) * ∏ x ∈ e.support, Psi isVec S (X x) ^ e x := by
  rw [monomial_eq, map_mul, Psi_C, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem Psi_low {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∉ S → e (j, a) = 0) (c : k) :
    Psi isVec S (monomial e c) ∈ supported (GenField k n) (loSet n S) := by
  rw [Psi_monomial]
  refine Subalgebra.mul_mem _ (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun x hx => Subalgebra.pow_mem _ ?_ _)
  obtain ⟨j, a⟩ := x
  have hj : j ∈ S := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hx) (he j a h)
  exact Psi_X_low isVec S hj a

theorem Psi_high {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    Psi isVec S (monomial e (1 : k)) = monomial (e.mapDomain Sum.inl) 1 := by
  rw [Psi_monomial, map_one, map_one, one_mul, ← rename_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [map_pow, rename_X]
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  rw [Psi_X_high isVec S hj a]

theorem wExp_add (last : Bool) (e f : LVar ℕ Empty n →₀ ℕ) :
    wExp isVec S last (e + f) = wExp isVec S last e + wExp isVec S last f := by
  simp only [wExp]
  change (e + f).sum (fun x d => (d : ℤ) * wtX isVec S last x) =
    e.sum (fun x d => (d : ℤ) * wtX isVec S last x) + f.sum (fun x d => (d : ℤ) * wtX isVec S last x)
  rw [Finsupp.sum_add_index']
  · intro x
    simp
  · intro x a b
    push_cast
    ring

theorem wExp_high (last : Bool) {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    wExp isVec S last (e.mapDomain Sum.inl : LVar ℕ Empty n →₀ ℕ) = 0 := by
  simp only [wExp]
  change (e.mapDomain Sum.inl).sum (fun x d => (d : ℤ) * wtX isVec S last x) = 0
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring)]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  simp [wtX, hj]

theorem Psi_Gc_low {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    Psi isVec S (Gc i G β) ∈ supported (GenField k n) (loSet n S) := by
  simp only [Gc, map_sum]
  exact Subalgebra.sum_mem _ fun e _ =>
    Psi_low isVec S (fun j a hj => by rw [lowerUnipotent_symm_apply, if_neg ((hS j).not.mp hj)]) _

theorem high_zero {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) {G : MvPolynomial (ℕ × Fin n) k} {β : ℕ × Fin n →₀ ℕ}
    (hβ : β ∈ G.support.image (highP i)) : ∀ j a, j ∈ S → β (j, a) = 0 := by
  intro j a hj
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hβ
  rw [highPart_apply, if_pos ((hS j).mp hj)]

theorem Psi_decomp {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) :
    Psi isVec S G = ∑ β ∈ G.support.image (highP i),
      Psi isVec S (Gc i G β) * monomial (β.mapDomain Sum.inl) 1 := by
  conv_lhs => rw [decomp i G]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [map_mul, Psi_high isVec S (high_zero S hS hβ)]

theorem supp_sub {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (G : MvPolynomial (ℕ × Fin n) k)
    {β : ℕ × Fin n →₀ ℕ} (hβ : β ∈ G.support.image (highP i)) :
    (genAct (ζ := Empty) k isVec S last (rename Sum.inl (Gc i G β))).coeff.support ⊆
      (genAct (ζ := Empty) k isVec S last (rename Sum.inl G)).coeff.support := by
  intro j hj
  rw [gen_mem_supp] at hj ⊢
  obtain ⟨e, he, rfl⟩ := hj
  refine ⟨e + β.mapDomain Sum.inl, ?_, ?_⟩
  · rw [← Psi_apply] at he ⊢
    rw [Psi_decomp isVec S hS G]
    refine coeff_key (loSet n S) (G.support.image (highP i)) (fun γ => Psi isVec S (Gc i G γ))
      (fun γ => γ.mapDomain Sum.inl) (fun γ _ => Psi_Gc_low isVec S hS G γ) ?_
      (fun γ _ δ _ h => Finsupp.mapDomain_injective Sum.inl_injective h) hβ he
    intro γ hγ x hx
    obtain ⟨j', a, hj', rfl⟩ := hx
    rw [Finsupp.mapDomain_apply Sum.inl_injective]
    exact high_zero S hS hγ j' a hj'
  · rw [wExp_add, wExp_high isVec S last (high_zero S hS hβ), add_zero]

end LowHighPartSplit

open LowHighPartSplit in
theorem factSplit_valid : FactSplit := by
  intro k _ n N i isVec B θ M G hiN hG
  refine ⟨G.support.image (highP i), Gc i G, ?_, ?_, decomp i G, ?_⟩
  · intro β hβ j
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hβ
    have h := (mem_polB.mp hG) e he j
    simp only [highPart_apply]
    by_cases hji : j < i
    · simp only [if_pos hji, Finset.sum_const_zero]
      rw [if_neg (by omega)]
    · simp only [if_neg hji]
      rw [h]
      by_cases hjN : j < N
      · rw [if_pos hjN, if_pos ⟨by omega, hjN⟩]
      · rw [if_neg hjN, if_neg (by omega)]
  · intro β hβ
    rw [mem_polB]
    intro e he j
    have he2 : e ∈ (∑ e ∈ G.support.filter (fun e => highP i e = β),
        monomial (lowP i e) (coeff e G)).support := he
    have hsub := Finset.mem_of_subset support_sum he2
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hsub
    obtain ⟨e', ⟨he', -⟩, hmem⟩ := hsub
    rw [Finset.mem_singleton.mp (support_monomial_subset hmem)]
    simp only [lowerUnipotent_symm_apply]
    have h := (mem_polB.mp hG) e' he' j
    by_cases hji : j < i
    · simp only [if_pos hji]
      rw [h, if_pos (by omega : j < N)]
    · simp only [if_neg hji, Finset.sum_const_zero]
  · intro hgood β hβ
    obtain ⟨h1, h2⟩ := hgood
    have hS : ∀ j, j ∈ {j : ℕ | j < i} ↔ j < i := fun j => Iff.rfl
    exact ⟨fun t ht => le_trans (h1 t ht) (Finset.min_mono (supp_sub isVec {j : ℕ | j < i} hS true G hβ)),
      fun t ht => le_trans (Finset.max_mono (supp_sub isVec {j : ℕ | j < i} hS false G hβ)) (h2 t ht)⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
