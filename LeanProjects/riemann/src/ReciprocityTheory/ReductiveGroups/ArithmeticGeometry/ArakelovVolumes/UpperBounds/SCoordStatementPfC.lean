import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {ιB : Type} [Fintype ιB]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eval₂Hom_comp (φ : Ω →+* ℂ) (y : ιB → Ω) :
    eval₂Hom (φ.comp (algebraMap K Ω)) (φ ∘ y) = φ.comp (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp
  · intro b; simp

def coef (y : ιB → Ω) (a : Ω) (P : Polynomial (MvPolynomial ιB K)) (b : ιB) : Ω :=
  -(xTerm (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a b P) /
    (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a

theorem deriv_rel (φ : Ω →+* ℂ) {y : ιB → Ω} {a : Ω} (P : Polynomial (MvPolynomial ιB K))
    (hP' : (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a ≠ 0)
    {h : V → ιB → ℂ} {g : V → ℂ} {Dh : ιB → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ b, HasFDerivAt (fun z => h z b) (Dh b) 0) (hg : HasFDerivAt g Dg 0)
    (h0 : h 0 = φ ∘ y) (g0 : g 0 = φ a)
    (hrel : ∀ᶠ z in 𝓝 (0 : V), P.eval₂ (eval₂Hom (φ.comp (algebraMap K Ω)) (h z)) (g z) = 0) :
    Dg = ∑ b, φ (coef y a P b) • Dh b := by
  set σ := φ.comp (algebraMap K Ω)
  have hd := hasFDerivAt_eval₂ σ P hh hg
  have hz : HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z)) (0 : V →L[ℂ] ℂ) 0 :=
    (hasFDerivAt_const (0 : ℂ) (0 : V)).congr_of_eventuallyEq (hrel.mono fun z hz => hz)
  have heq := hd.unique hz
  rw [h0, g0, eval₂Hom_comp] at heq
  simp only [← Polynomial.hom_eval₂, ← map_xTerm] at heq
  set E := (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a
  have hE : φ E ≠ 0 := (map_ne_zero φ).mpr hP'
  apply smul_right_injective (V →L[ℂ] ℂ) hE
  simp only
  rw [eq_neg_of_add_eq_zero_left heq, Finset.smul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, coef, map_div₀, map_neg, mul_div_cancel₀ _ hE, neg_smul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC
