import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Pin1

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexConjugate

namespace Pin2

theorem star_real_smul {g : ℕ} (t : ℝ) (v : Fin g → ℂ) : star ((t : ℂ) • v) = (t : ℂ) • star v := by
  ext i
  simp

theorem form_zero {g : ℕ} (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (addL : ∀ z z' w, D (z + z') w = D z w + D z' w) (smulL : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (addR : ∀ z w w', D z (w + w') = D z w + D z w') (smulR : ∀ (t : ℝ) z w, D z ((t : ℂ) • w) = t * D z w)
    (h0 : ∀ p ∈ S, ∀ q ∈ S, (D (star p) (star q)).im = 0) (z w : Fin g → ℂ) : D z w = 0 := by
  have hrs : ∀ (t : ℝ) (u : Fin g → ℂ), t • u = (t : ℂ) • u := fun t u => by
    ext i
    simp [Complex.real_smul]
  have hstar_smul : ∀ (t : ℝ) (u : Fin g → ℂ), star (t • u) = t • star u := fun t u => by
    rw [hrs, hrs, star_real_smul]
  have hD0 : ∀ u, D 0 u = 0 := fun u => by simpa using smulL 0 0 u
  have hD0' : ∀ u, D u 0 = 0 := fun u => by simpa using smulR 0 u 0

  let N1 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {u | ∀ q ∈ S, (D (star u) (star q)).im = 0}
      add_mem' := by
        intro a b ha hb q hq
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addL, Complex.add_im, ha q hq, hb q hq, add_zero]
      zero_mem' := by
        intro q _
        rw [star_zero, hD0, Complex.zero_im]
      smul_mem' := by
        intro t a ha q hq
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulL, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha q hq, mul_zero,
          zero_mul, add_zero] }
  have hN1 : ∀ u, u ∈ N1 := by
    intro u
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N1 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ q ∈ S, _
      exact h0 p hp
    exact h Submodule.mem_top
  have h1 : ∀ u, ∀ q ∈ S, (D u (star q)).im = 0 := by
    intro u
    have hm : ∀ q ∈ S, (D (star (star u)) (star q)).im = 0 := hN1 (star u)
    rw [star_star] at hm
    exact hm

  let N2 : Submodule ℝ (Fin g → ℂ) :=
    { carrier := {q | ∀ u, (D u (star q)).im = 0}
      add_mem' := by
        intro a b ha hb u
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [star_add, addR, Complex.add_im, ha u, hb u, add_zero]
      zero_mem' := by
        intro u
        rw [star_zero, hD0', Complex.zero_im]
      smul_mem' := by
        intro t a ha u
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hstar_smul, hrs, smulR, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha u, mul_zero,
          zero_mul, add_zero] }
  have hN2 : ∀ q, q ∈ N2 := by
    intro q
    have h : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ N2 := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      intro p hp
      show ∀ u, _
      exact fun u => h1 u p hp
    exact h Submodule.mem_top
  have h2 : ∀ u q, (D u q).im = 0 := by
    intro u q
    have hm : ∀ u, (D u (star (star q))).im = 0 := hN2 (star q)
    rw [star_star] at hm
    exact hm u
  have hre : (D z w).re = 0 := by
    have h := h2 (Complex.I • z) w
    rw [smulL, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h
    exact h
  exact Complex.ext_iff.2 ⟨by simp [hre], by simp [h2 z w]⟩

section Hf

variable {ι : Type} [Fintype ι]

theorem hf_add_left (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_add_right (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_smul_left (t : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (t • v) w = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_real_smul_right (t : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v ((t : ℂ) • w) = t * Hf v w := by
  unfold Hf
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]

theorem hf_re_nonneg (v : EuclideanSpace ℂ ι) : 0 ≤ (Hf v v).re := by
  unfold Hf
  simp [inner_self_nonneg]
  exact Finset.sum_nonneg fun x _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

end Hf

section HermForm

variable {g : ℕ}

theorem hm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

theorem hm_real_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  simp [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul]

end HermForm

end Pin2

section Pin2

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem lattice_trace_imaginary_part (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (a b : (W.F.Di (W.ik k)).La) :
    (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b)))).im =
        A.sg * ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) ∧
      (star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im =
        ((Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm ((W.φ k a : (U.X k).Λ) : Fin r → E)
          ((W.φ k b : (U.X k).Λ) : Fin r → E)) : ℚ) : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [← pin1 hU hσ W A hx a, ← pin1 hU hσ W A hx b]
    exact A.im_eq _ (W.φ k a).2 _ (W.φ k b).2
  · rw [star_star, star_star, Complex.star_def, Complex.conj_im, Wu.c1]
    have hi := W.isom k a b
    rw [neg_mul, map_neg] at hi
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hi
    push_cast at hr
    linarith

theorem pin2 (hx : (U.X k).IsOrtho x.1) (Wu : UnitAt W) (z z' : Fin W.g → ℂ) :
    Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') = star (hermForm Wu.Hm (star z) (star z')) := by
  have key : ∀ z z', Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
      (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')) = 0 := by
    intro z z'
    refine Pin2.form_zero (fun z z' => Hf (Lmap hU hσ W A z) (Lmap hU hσ W A z') -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star z) (star z')))
      (Set.range W.Pm) W.per.2.2.2.1 ?_ ?_ ?_ ?_ ?_ z z'
    · intro z z' w
      simp only [map_add, Pin2.hf_add_left, star_add, Pin2.hm_add_left]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_smul_left, star_smul, Pin2.hm_smul_left, star_mul', star_star]
      ring
    · intro z w w'
      simp only [map_add, Pin2.hf_add_right, star_add, Pin2.hm_add_right]
      ring
    · intro t z w
      simp only [map_smul, Pin2.hf_real_smul_right, Pin2.star_real_smul, Pin2.hm_real_smul_right, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      ring
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      obtain ⟨h1, h2⟩ := lattice_trace_imaginary_part hU hσ W A hx Wu a b
      show (Hf (Lmap hU hσ W A (star (W.Pm a))) (Lmap hU hσ W A (star (W.Pm b))) -
        (A.sg : ℂ) * star (hermForm Wu.Hm (star (star (W.Pm a))) (star (star (W.Pm b))))).im = 0
      rw [Complex.sub_im, Complex.im_ofReal_mul, h1, h2]
      ring
  rcases A.sg_pm with h | h
  · have := key z z'
    rw [h, Complex.ofReal_one, _root_.one_mul, sub_eq_zero] at this
    exact this
  · rcases Nat.eq_zero_or_pos W.g with hg | hg
    · have hz : ∀ v : Fin W.g → ℂ, v = 0 := fun v => funext fun i => absurd i.2 (by omega)
      rw [hz z, hz z', map_zero]
      simp [Hf, hermForm]
    · exfalso
      obtain ⟨v, hv⟩ : ∃ v : Fin W.g → ℂ, v = Pi.single (⟨0, hg⟩ : Fin W.g) 1 := ⟨_, rfl⟩
      have hv0 : star v ≠ 0 := by
        intro h0
        have := congrFun h0 ⟨0, hg⟩
        simp [hv] at this
      have hpos := Wu.pos (star v) hv0
      have hk := key v v
      rw [h, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_neg_eq_add] at hk
      have hre := congrArg Complex.re hk
      rw [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
      linarith [Pin2.hf_re_nonneg (Lmap hU hσ W A v)]

end Pin2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
