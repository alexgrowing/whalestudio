import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

private def reHermBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).re)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

private theorem hermForm_swap' {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

private theorem form_eq_zero_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

private theorem hermForm_adj_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span' s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add, l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add, l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem gram_re_posdef_adj : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P →
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧
      ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  intro O _ bar g ρ D P r e hP
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hE⟩ := hP
  set B := reHermBilin Hm with hBdef
  have hB : ∀ z w, B z w = (hermForm Hm z w).re := fun _ _ => rfl
  have hind : LinearIndependent ℝ (fun i => P (e i)) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    let bL := e.map (LinearEquiv.ofInjective P.toIntLinearMap hinj)
    have hfun : (fun i => P (e i)) = ⇑(bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)) := by
      funext i
      rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
      rfl
    rw [hfun]
    exact (bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)).linearIndependent
  have hBpos : ∀ v, v ≠ 0 → 0 < B v v := fun v hv => hpos v hv
  have hBnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (hBpos v hv).le
  have hBsymm : ∀ v w, B v w = B w v := fun v w => by
    rw [hB, hB, hermForm_swap' hH v w]; simp
  refine ⟨Matrix.of fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hBsymm]
  · intro z hz
    have hexp : ∀ x : Fin r → ℝ, B (∑ j, x j • P (e j)) (∑ j, x j • P (e j)) =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * (x i * x j) := by
      intro x
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hBsymm (P (e j))]
      ring
    have hq : (star z ⬝ᵥ (Matrix.of (fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ)) *ᵥ z)).re =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).re * (z j).re) +
          ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).im * (z j).im) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Complex.re_sum, Finset.mul_sum, Pi.star_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hq, ← hexp, ← hexp]
    have hor : (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      funext i
      exact Complex.ext (congrFun h.1 i) (congrFun h.2 i)
    rcases hor with h | h
    · have hv : ∑ j, (z j).re • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_pos_of_nonneg (hBpos _ hv) (hBnn _)
    · have hv : ∑ j, (z j).im • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_nonneg_of_pos (hBnn _) (hBpos _ hv)
  · intro a
    have hadj : ∀ z w, hermForm Hm (ρ a *ᵥ z) w = hermForm Hm z (ρ (bar a) *ᵥ w) :=
      hermForm_adj_of_im_span' (Set.range P) hspan Hm (Matrix.mulVecLin (ρ a)) (Matrix.mulVecLin (ρ (bar a))) (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        simp only [Matrix.mulVecLin_apply]
        rw [← hlin, ← hlin, hE, hE, D.adj])
    have hexpand : ∀ v : D.La, P v = ∑ k, e.repr v k • P (e k) := fun v => by
      conv_lhs => rw [← e.sum_repr v]
      simp only [map_sum, map_zsmul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, actM, Matrix.conjTranspose_apply, star_intCast]
    have h1 : B (P (e i)) (P (bar a • e j)) = ∑ k, B (P (e i)) (P (e k)) * (e.repr (bar a • e j) k : ℝ) := by
      rw [hexpand (bar a • e j), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]
    have h2 : B (P (a • e i)) (P (e j)) = ∑ k, (e.repr (a • e i) k : ℝ) * B (P (e k)) (P (e j)) := by
      rw [hBsymm, hexpand (a • e i), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hBsymm]
    have h3 : B (P (e i)) (P (bar a • e j)) = B (P (a • e i)) (P (e j)) := by
      rw [hB, hB, hlin, hlin, hadj]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1.symm.trans (h3.trans h2))
    push_cast at this
    exact this

end GlobalTheory.PELU
