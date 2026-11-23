import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsMultiHomogIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ W

def chartIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  P ⊔ Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev chartRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) : Type :=
  MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p

theorem eval_smul_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → ℂ) (y : (Σ k, ι k) → ℂ) :
    eval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval y f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hc : ∏ q : (Σ k, ι k), c q.1 ^ d q = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have key : ∏ q, (c q.1 * y q) ^ d q = (∏ k, c k ^ a k) * ∏ q, y q ^ d q := by
    rw [← hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun q _ => mul_pow _ _ _)
  linear_combination (coeff d f) * key

theorem eval_eq_zero_of_smul {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (c : K → ℂ) (y : (Σ k, ι k) → ℂ) (hy : ∀ f ∈ P, eval y f = 0) :
    ∀ f ∈ P, eval (fun q => c q.1 * y q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hP
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha⟩ := hS g hg
    rw [eval_smul_of_isMultiHomog ha, hy g (Ideal.subset_span hg), mul_zero]
  | zero => simp
  | add g h _ _ hg hh => rw [map_add, hg, hh, add_zero]
  | smul a g _ hg => rw [smul_eq_mul, map_mul, hg, mul_zero]

theorem mem_conePts_iff_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts P ↔ ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 := by
  have haff : affCoord p z = fun q => (z ⟨q.1, p q.1⟩)⁻¹ * z q := by
    funext q
    show z q / z ⟨q.1, p q.1⟩ = _
    rw [div_eq_inv_mul]
  unfold conePts
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hzP⟩
    have hle : chartIdeal P p ≤ RingHom.ker (eval (affCoord p z)) := by
      refine sup_le ?_ ?_
      · intro f hf
        rw [RingHom.mem_ker, haff]
        exact eval_eq_zero_of_smul hP (fun k => (z ⟨k, p k⟩)⁻¹) z hzP f hf
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        show z ⟨k, p k⟩ / z ⟨k, p k⟩ - 1 = 0
        rw [div_self (hz k), sub_self]
    intro h hh
    exact hle hh
  · intro hch
    refine ⟨fun k => ⟨p k, hz k⟩, ?_⟩
    have hzeq : z = fun q => z ⟨q.1, p q.1⟩ * affCoord p z q := by
      funext q
      show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
      have := hz q.1
      field_simp
    intro f hf
    rw [hzeq]
    exact eval_eq_zero_of_smul hP (fun k => z ⟨k, p k⟩) (affCoord p z)
      (fun g hg => hch g (Ideal.mem_sup_left hg)) f hf

theorem conePts_of_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) (hy : ∀ h ∈ chartIdeal P p, eval y h = 0) :
    y ∈ conePts P ∧ (∀ k, y ⟨k, p k⟩ = 1) ∧ affCoord p y = y := by
  have hle : Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) ≤
      chartIdeal P p := le_sup_right
  have hleP : P ≤ chartIdeal P p := le_sup_left
  have h1 : ∀ k, y ⟨k, p k⟩ = 1 := by
    intro k
    have hmem : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      hle (Ideal.subset_span (Set.mem_range_self k))
    have := hy _ hmem
    rw [map_sub, eval_X, map_one, sub_eq_zero] at this
    exact this
  refine ⟨?_, h1, ?_⟩
  · unfold conePts
    rw [Set.mem_setOf_eq]
    exact ⟨fun k => ⟨p k, by rw [h1 k]; exact one_ne_zero⟩, fun f hf => hy f (hleP hf)⟩
  · funext q
    show y q / y ⟨q.1, p q.1⟩ = y q
    rw [h1 q.1, div_one]

theorem exists_chart (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ p : (k : K) → ι k, (∀ k, z ⟨k, p k⟩ ≠ 0) ∧ ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, p k⟩‖ := by
  have hmax : ∀ k, ∃ i, ∀ j, ‖z ⟨k, j⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun j => ‖z ⟨k, j⟩‖)
  choose p hp using hmax
  refine ⟨p, fun k => ?_, fun k i => hp k i⟩
  obtain ⟨i0, hi0⟩ := hz k
  have h1 : 0 < ‖z ⟨k, i0⟩‖ := norm_pos_iff.mpr hi0
  have h2 := hp k i0
  intro h
  rw [h, norm_zero] at h2
  linarith

theorem affCoord_eq_of_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  show c q.1 * z' q / (c q.1 * z' ⟨q.1, p q.1⟩) = z' q / z' ⟨q.1, p q.1⟩
  exact mul_div_mul_left (z' q) (z' ⟨q.1, p q.1⟩) (hc q.1)

theorem sameOrbit_affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (affCoord p z) := by
  refine ⟨fun k => z ⟨k, p k⟩, hz, ?_⟩
  funext q
  show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
  have := hz q.1
  field_simp

end

end ReciprocityTheory.AnForm.R
