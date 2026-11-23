import Mathlib
namespace FunctorialResolution.EmbeddedResolution

private theorem prod_notMem_of_isPrime {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {I : Ideal R} (hI : I.IsPrime) (g : ι → R) (t : Finset ι) :
    (∀ j ∈ t, g j ∉ I) → ∏ j ∈ t, g j ∉ I := by
  induction t using Finset.induction_on with
  | empty =>
      intro _ h1
      rw [Finset.prod_empty] at h1
      refine hI.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      exact h1
  | @insert a u ha ih =>
      intro h hmem
      rw [Finset.prod_insert ha] at hmem
      rcases hI.mem_or_mem hmem with h1 | h1
      · exact h a (Finset.mem_insert_self a u) h1
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) h1

private theorem span_singleton_mul_eq_inf {R : Type*} [CommRing R] {a b : R}
    (hpa : (Ideal.span ({a} : Set R)).IsPrime) (hb : b ∉ Ideal.span ({a} : Set R)) :
    Ideal.span ({a * b} : Set R) = Ideal.span ({a} : Set R) ⊓ Ideal.span ({b} : Set R) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨a, mul_comm a b⟩
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hz2
    have hv : v ∈ Ideal.span ({a} : Set R) := (hpa.mem_or_mem hz1).resolve_left hb
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hv
    exact Ideal.mem_span_singleton.mpr ⟨w, by ring⟩

theorem span_singleton_prod_eq_biInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by
  revert hp hdvd
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert a u ha ih =>
      intro hp hdvd
      have hpa : (Ideal.span ({f a} : Set R)).IsPrime := hp a (Finset.mem_insert_self a u)
      have hP : (∏ i ∈ u, f i) ∉ Ideal.span ({f a} : Set R) := by
        refine prod_notMem_of_isPrime hpa f u ?_
        intro j hj
        exact hdvd a (Finset.mem_insert_self a u) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      have ihu := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          hdvd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      rw [Finset.prod_insert ha, span_singleton_mul_eq_inf hpa hP, ihu, Finset.iInf_insert]

theorem isRadical_biInf_span_singleton {R : Type*} [CommRing R] {ι : Type*}
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) :
    (⨅ i ∈ s, Ideal.span ({f i} : Set R)).IsRadical := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  refine le_trans (Ideal.radical_mono ?_) (hp i hi).isRadical
  exact iInf_le_of_le i (iInf_le _ hi)

theorem isRadical_span_singleton_prod_finset {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by
  rw [span_singleton_prod_eq_biInf f s hp hdvd]
  exact isRadical_biInf_span_singleton f s hp

end FunctorialResolution.EmbeddedResolution

namespace IsLocalization

theorem map_eq_map_of_map_eq_map {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by
  have he : ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom).comp (algebraMap R S)
      = algebraMap R T :=
    RingHom.ext fun r => by
      show (IsLocalization.algEquiv M S T) (algebraMap R S r) = algebraMap R T r
      exact (IsLocalization.algEquiv M S T).commutes r
  have hmap : ∀ K : Ideal R, Ideal.map (algebraMap R T) K =
      Ideal.map ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom)
        (Ideal.map (algebraMap R S) K) := by
    intro K
    rw [Ideal.map_map, he]
  rw [hmap, hmap, h]

end IsLocalization

namespace Ideal

theorem list_prod_le_getElem {R : Type*} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by
  revert i hi
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons A L ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [List.prod_cons, List.getElem_cons_zero]
          exact le_trans Ideal.mul_le_inf inf_le_left
      | succ i' =>
          have hi' : i' < L.length := by simpa using hi
          simp only [List.prod_cons, List.getElem_cons_succ]
          exact le_trans (le_trans Ideal.mul_le_inf inf_le_right) (ih i' hi')

end Ideal

namespace KaehlerDifferential

theorem residue_tmul_D_mul_of_mem_maximalIdeal (k : Type*) [CommRing k] (A : Type*)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  have hsm : ∀ a : A, a • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A a := by
    intro a
    rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
  have hx0 : IsLocalRing.residue A x = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hstep : IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x)
      = (IsLocalRing.residue A c * 1) ⊗ₜ[A] KaehlerDifferential.D k A x := rfl
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, hsm, hsm, hx0, TensorProduct.zero_tmul, zero_add, hstep,
    mul_one]

end KaehlerDifferential
