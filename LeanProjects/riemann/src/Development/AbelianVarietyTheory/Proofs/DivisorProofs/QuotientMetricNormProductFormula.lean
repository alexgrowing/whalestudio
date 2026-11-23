import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem quotGram_pyth_rankTwo (G : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (hG : G.PosDef)
    (x : Fin 1 ⊕ Fin 1 → ℂ) (τ : ℂ) (v : Fin 1 → ℂ) (hv : v 0 = x (.inr 0)) :
    (form (quotGram G) v v).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re =
      (form G x x).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re -
        ‖form G x (Sum.elim (fun _ => τ) 0)‖ ^ 2 := by
  have hH := hG.isHermitian
  have h11 : G (.inl 0) (.inl 0) ≠ 0 := (hG.diag_pos (i := .inl 0)).ne'
  have hr : starRingEnd ℂ (G (.inl 0) (.inl 0)) = G (.inl 0) (.inl 0) := hH.apply _ _
  have h12 : G (.inl 0) (.inr 0) = starRingEnd ℂ (G (.inr 0) (.inl 0)) := (hH.apply _ _).symm
  have hinv : (G.toBlocks₁₁)⁻¹ 0 0 = (G (.inl 0) (.inl 0))⁻¹ := by
    rw [Matrix.inv_def, Matrix.det_unique, Matrix.adjugate_fin_one]
    simp [Matrix.toBlocks₁₁, Ring.inverse_eq_inv']
  obtain ⟨r, hr'⟩ : ∃ r : ℝ, G (.inl 0) (.inl 0) = r := ⟨_, (Complex.conj_eq_iff_re.1 hr).symm⟩
  simp only [form_eq_sum, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, mul_zero, add_zero,
    quotGram, Matrix.sub_apply, Matrix.mul_apply, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁,
    Matrix.toBlocks₁₂, Matrix.of_apply, Fin.default_eq_zero]
  rw [hinv, hv, h12]
  rw [hr'] at h11 ⊢
  generalize x (Sum.inl 0) = x₁ at ⊢
  generalize x (Sum.inr 0) = x₂ at ⊢
  generalize G (Sum.inr 0) (Sum.inl 0) = g at ⊢
  generalize G (Sum.inr 0) (Sum.inr 0) = d at ⊢
  have hr0 : (r : ℂ) ≠ 0 := h11
  have hB : τ * (r : ℂ) * starRingEnd ℂ τ + 0 * g * starRingEnd ℂ τ =
      ((r * Complex.normSq τ : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.mul_conj]; ring
  have hn (z : ℂ) : ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hB, Complex.ofReal_re, hn, ← Complex.re_mul_ofReal, ← Complex.re_mul_ofReal, ← Complex.sub_re]
  congr 1
  simp only [Complex.ofReal_mul, ← Complex.mul_conj, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]
  field_simp
  ring

theorem quot_form_pyth_rankTwo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)),
    IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U,
      ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re =
        (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  intro k _ X p σ S h hS h₁ h₃ U t w _ y hy
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  let u : Γ(S.X₂, U) → Fin 1 ⊕ Fin 1 → ℂ := fun s i => (a.mid hS).crd p σ s y (finSumFinEquiv i)
  have hform (s s' : Γ(S.X₂, U)) : h.form s s' y = form (h.gram a.frame y) (u s) (u s') := by
    rw [h.form_eq (a.mid hS) ha s s' hy, h.gram_frame hS a ha, form_eq_sum, form_eq_sum,
      ← finSumFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← finSumFinEquiv.sum_comp]
    rfl
  have hf : u (S.f.app U t) = Sum.elim (fun _ => a.sub.crd p σ t y 0) 0 := by
    funext i
    refine (congrFun ((a.mid hS).crd_app a.sub S.f t hy ha) (finSumFinEquiv i)).trans ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one]
    have e := a.crd_frame hS ha i (.inl 0)
    refine (congrArg (· * _) e).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply, Subsingleton.elim i 0]
  have hg : a.quot.crd p σ (S.g.app U w) y 0 = u w (.inr 0) := by
    refine (congrFun (a.quot.crd_app (a.mid hS) S.g w hy ha) 0).trans ?_
    have e₃ (b) : (a.mid hS).e (finSumFinEquiv b) = a.frame b := by simp [VBExt.AdaptedChart.mid]
    have e₁ : a.quot.crd p σ (S.g.app a.U (a.frame (.inl 0))) y = 0 := by
      rw [show S.g.app a.U (a.frame (.inl 0)) = 0 from congr(($(S.zero)).app a.U (a.e 0)),
        Chart.crd_zero]
    have e₂ : a.quot.crd p σ (S.g.app a.U (a.frame (.inr 0))) y = Pi.single 0 1 :=
      a.quot.crd_frame ha 0
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
    refine (congrArg₂ (· + ·) (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₁) 0))
      (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₂) 0))).trans ?_
    simp [u]
  have hq : (h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y =
      form (quotGram (h.gram a.frame y)) (a.quot.crd p σ (S.g.app U w) y)
        (a.quot.crd p σ (S.g.app U w) y) := by
    rw [(h.quot hS h₁ h₃).form_eq a.quot ha _ _ hy, h.quot_G hS h₁ h₃ a ha]
  rw [hq, hform, hform, hform, hf]
  exact quotGram_pyth_rankTwo _ (h.posDef_gram_frame hS a ha) _ _ _ hg

end GlobalTheory.CurveDens
