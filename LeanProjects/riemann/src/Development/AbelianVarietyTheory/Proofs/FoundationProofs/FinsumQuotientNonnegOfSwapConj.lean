import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem sum_nonneg_of_swap_conj_fintype (Q : Type) [AddCommGroup Q] [Fintype Q] (ψ : Q → ℂ)
    (P S L : Q →+ Q) (hL : Function.Injective L)
    (hP : ∀ x, P (P x) = P x) (hS : ∀ x, S (S x) = x)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hLP : ∀ x, L (P x) = P (L x))
    (hψ : ∀ x, ψ x = ψ (P x) * ψ (x - P x)) (hψS : ∀ x, ψ (S x) = ψ x)
    (hψL : ∀ x, ψ (L x) = (starRingEnd ℂ) (ψ x)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ q : Q, ψ q = (r : ℂ) := by
  set A : Finset Q := Finset.univ.filter (fun x => P x = x) with hA
  set A' : Finset Q := Finset.univ.filter (fun x => P x = 0) with hA'
  have mA : ∀ x, x ∈ A ↔ P x = x := by intro x; simp [hA]
  have mA' : ∀ x, x ∈ A' ↔ P x = 0 := by intro x; simp [hA']
  have h1 : ∑ q : Q, ψ q = ∑ p ∈ A ×ˢ A', ψ p.1 * ψ p.2 := by
    refine Finset.sum_nbij' (fun q => (P q, q - P q)) (fun p => p.1 + p.2) ?_ ?_ ?_ ?_ ?_
    · intro q _
      simp [Finset.mem_product, mA, mA', hP]
    · intro p _
      exact Finset.mem_univ _
    · intro q _
      simp
    · intro p hp
      rw [Finset.mem_product, mA, mA'] at hp
      ext <;> simp [hp.1, hp.2]
    · intro q _
      exact hψ q
  have h2 : ∑ x ∈ A', ψ x = ∑ x ∈ A, ψ x := by
    refine Finset.sum_nbij' S S ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA'] at hx
      rw [mA]
      have := hSP x
      rw [hx, map_zero] at this
      exact (sub_eq_zero.mp this.symm).symm
    · intro x hx
      rw [mA] at hx
      rw [mA']
      have := hSP x
      rw [hx] at this
      exact sub_eq_self.mp this.symm
    · intro x _
      exact hS x
    · intro x _
      exact hS x
    · intro x _
      exact (hψS x).symm
  have h3 : (starRingEnd ℂ) (∑ x ∈ A, ψ x) = ∑ x ∈ A, ψ x := by
    rw [map_sum]
    refine Finset.sum_bij (fun x _ => L x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA] at hx
      rw [mA, ← hLP, hx]
    · intro x _ y _ h
      exact hL h
    · intro y hy
      obtain ⟨x, rfl⟩ := (Finite.injective_iff_surjective.mp hL) y
      refine ⟨x, ?_, rfl⟩
      rw [mA] at hy ⊢
      apply hL
      rw [hLP, hy]
    · intro x _
      exact (hψL x).symm
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp h3
  refine ⟨t * t, mul_self_nonneg t, ?_⟩
  rw [h1, Finset.sum_product, ← Finset.sum_mul_sum, h2, ht]
  push_cast
  rfl

theorem finsum_quotient_nonneg_of_swap_conj :
    ∀ (G : Type) [AddCommGroup G] (B : AddSubgroup G) [Finite (G ⧸ B)] (φ : G → ℂ) (P S L : G →+ G), (∀ x, ∀ w ∈ B, φ (x + w) = φ x) → (∀ w ∈ B, P w ∈ B ∧ S w ∈ B) → (∀ x, L x ∈ B ↔ x ∈ B) → (∀ x, P (P x) = P x) → (∀ x, S (S x) = x) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, L (P x) = P (L x)) → (∀ x, φ x = φ (P x) * φ (x - P x)) → (∀ x, φ (S x) = φ x) → (∀ x, φ (L x) = (starRingEnd ℂ) (φ x)) → ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : G ⧸ B, φ q.out = (r : ℂ) := by
  intro G _ B _ φ P S L hper hB hLB hP hS hSP hLP hφ hφS hφL
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite _
  have hout : ∀ x : G, φ (QuotientAddGroup.mk x : G ⧸ B).out = φ x := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_out_eq_mul B x
    rw [hw]
    exact hper x w w.2
  let P' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B P (fun w hw => (hB w hw).1)
  let S' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B S (fun w hw => (hB w hw).2)
  let L' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B L (fun w hw => (hLB w).2 hw)
  have eP : ∀ x : G, P' (x : G ⧸ B) = (P x : G) := fun x => rfl
  have eS : ∀ x : G, S' (x : G ⧸ B) = (S x : G) := fun x => rfl
  have eL : ∀ x : G, L' (x : G ⧸ B) = (L x : G) := fun x => rfl
  rw [finsum_eq_sum_of_fintype]
  refine sum_nonneg_of_swap_conj_fintype (G ⧸ B) (fun q => φ q.out) P' S' L' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [eL, QuotientAddGroup.eq_zero_iff] at hq
      exact (QuotientAddGroup.eq_zero_iff x).2 ((hLB x).1 hq)
  all_goals
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      simp only [eP, eS, eL, ← QuotientAddGroup.mk_sub, hout]
      first
        | rw [hP]
        | rw [hS]
        | rw [hSP]
        | rw [hLP]
        | exact hφ x
        | exact hφS x
        | exact hφL x

end GlobalTheory
