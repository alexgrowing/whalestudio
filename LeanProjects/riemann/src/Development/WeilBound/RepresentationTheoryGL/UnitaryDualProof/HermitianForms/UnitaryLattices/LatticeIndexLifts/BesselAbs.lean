import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.SummandInv

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem B_u (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : (Fin n → k) → ℂ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (T : Finset (Fin n → k)) (v w : V) :
    B (∑ t ∈ T, c t • col t v) w = ∑ t ∈ T, c t * B (col t v) w := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem gram (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A H : AddSubgroup (Fin n → k)) (hHA : H ≤ A) (T : Finset (Fin n → k))
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (v : V) (hv : ∀ a ∈ H, col a v = v) (ξ ζ : Fin n → k) (hξ : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    B (∑ t ∈ T, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v)
        (∑ r ∈ T, (starRingEnd ℂ ((φ (ζ ⬝ᵥ r) : Circle) : ℂ)) • col r v)
      = (∑ r ∈ T, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
          ∑ t ∈ T, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) * B (col t v) v := by
  classical
  set f : (Fin n → k) → ℂ := fun x => starRingEnd ℂ ((φ (ξ ⬝ᵥ x) : Circle) : ℂ) * B (col x v) v with hf
  have hfH : ∀ x h, h ∈ H → f (x + h) = f x := by
    intro x h hh
    simp only [hf, dotProduct_add, AddChar.map_add_eq_mul, hξ h hh, mul_one, hca, hv h hh]
  have hsh : ∀ r ∈ T, ∑ t ∈ T, f (t + -r) = ∑ t ∈ T, f t := fun r hr =>
    sum_transl A H hHA T hT hu f hfH (-r) (A.neg_mem (hT r hr))
  have key : ∀ t r, B (col t v) (col r v) = B (col (t - r) v) v := by
    intro t r
    have h1 : col t v = col r (col (t - r) v) := by rw [← hca, add_sub_cancel]
    rw [h1, hBc]
  have hsplit : ∀ t r, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) =
      starRingEnd ℂ ((φ (ξ ⬝ᵥ (t + -r)) : Circle) : ℂ) * starRingEnd ℂ ((φ (ξ ⬝ᵥ r) : Circle) : ℂ) := by
    intro t r
    rw [← map_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← dotProduct_add, neg_add_cancel_right]
  conv_lhs =>
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_self_apply, RingHom.id_apply, key, Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← hsh r hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hsplit t r]
  simp only [hf, Circle.coe_mul, Circle.coe_inv_eq_conj, sub_eq_add_neg]
  ring

theorem gram_av (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (ξ ζ : Fin n → k) (v : V)
    (p : AddSubgroup (Fin n → k) × Finset (Fin n → k)) (hpξ : AD φ col ξ A v p) (hpζ : AD φ col ζ A v p) :
    B (av φ col ξ A v) (av φ col ζ A v) =
      ((p.2.card : ℂ)⁻¹ * ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
        B (av φ col ξ A v) v := by
  rw [av_eq' φ col hca A ξ v p hpξ, av_eq' φ col hca A ζ v p hpζ]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hpξ
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    gram φ col hc0 hca B hBc A p.1 h1 p.2 h5 h6 v h3 ξ ζ h4, LinearMap.smul_apply, B_u]
  simp only [smul_eq_mul, map_inv₀, map_natCast]
  ring

theorem bessel_abs (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → V) (v : V)
    (hw : ∀ i ∈ s, ∀ j ∈ s, B (w i) (w j) = if i = j then B (w i) v else 0) :
    ∑ i ∈ s, (B (w i) v).re ≤ (B v v).re := by
  classical
  have hWW : B (∑ i ∈ s, w i) (∑ i ∈ s, w i) = ∑ i ∈ s, B (w i) v := by
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_congr rfl fun d hd => hw d hd i hi]
    simp [hi]
  have hWv : B (∑ i ∈ s, w i) v = ∑ i ∈ s, B (w i) v := by
    simp only [map_sum, LinearMap.sum_apply]
  have hvW : B v (∑ i ∈ s, w i) = starRingEnd ℂ (∑ i ∈ s, B (w i) v) := by
    rw [hB.1 (∑ i ∈ s, w i) v, hWv]
  have h0 := hB.2 (v - ∑ i ∈ s, w i)
  simp only [map_sub, LinearMap.sub_apply, hWW, hWv, hvW, Complex.sub_re, Complex.conj_re] at h0
  rw [← Complex.re_sum]
  linarith

theorem av_bessel' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA s v
  refine bessel_abs B hB s (fun ξ => av φ col ξ A v) v ?_
  intro ξ hξ ξ' hξ'
  show B (av φ col ξ A v) (av φ col ξ' A v) = if ξ = ξ' then B (av φ col ξ A v) v else 0
  rw [gram_av φ col hc0 hca B hBc A ξ ξ' v p (hp ξ hξ) (hp ξ' hξ')]
  have hcard := card_ne_zero A p.1 p.2 (hp ξ hξ).2.2.2.2.2
  split_ifs with hxx
  · subst hxx
    simp only [inv_mul_cancel, Circle.coe_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hcard, one_mul]
  · have hz : ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r) : Circle)) : ℂ) = 0 := by
      obtain ⟨h1, -, -, h4, h5, h6⟩ := hp ξ hξ
      obtain ⟨-, -, -, h4', -, -⟩ := hp ξ' hξ'
      by_contra hne
      apply hxx
      apply hs ξ hξ ξ' hξ'
      show ∀ a ∈ A, φ ((ξ - ξ') ⬝ᵥ a) = 1
      intro a ha
      by_contra hna
      apply hne
      refine sum_circ_eq_zero A p.1 h1 p.2 h5 h6 (fun r => (φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r))
        (fun x y => circ_char φ φ ξ ξ' x y) (fun h hh => by simp [h4 h hh, h4' h hh]) a ha ?_
      intro hχ
      apply hna
      have e : φ (ξ ⬝ᵥ a) = φ (ξ' ⬝ᵥ a) := inv_mul_eq_one.mp hχ
      rw [sub_dotProduct, AddChar.map_sub_eq_div, e, div_self']
    rw [hz, mul_zero, zero_mul]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
