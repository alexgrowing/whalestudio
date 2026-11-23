import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FFirstProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FRedUnique

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem eq_single_of_monomial {ι σ : Type*} (Ψ : (ι →₀ ℤ) ≃+ MvPolynomial σ ℤ) (C : ι →₀ ℤ) (m : σ →₀ ℕ)
    (ep : Ψ C = MvPolynomial.monomial m 1) (hnn : ∀ w, 0 ≤ C w) (hU : ∀ w x, C w ≠ 0 → C x ≠ 0 → x = w) :
    ∃ w, C = Finsupp.single w 1 := by
  classical
  have hne : C ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ep
    exact one_ne_zero ((MvPolynomial.monomial_eq_zero).1 ep.symm)
  obtain ⟨w, hw⟩ : ∃ w, w ∈ C.support := Finsupp.support_nonempty_iff.2 hne
  have hw' := Finsupp.mem_support_iff.1 hw
  have h1 : C = C w • Finsupp.single w (1 : ℤ) := by
    ext x
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hx
    · rw [hx, smul_eq_mul, mul_one]
    · rw [smul_zero]
      by_contra hx0
      exact hx (hU w x hw' hx0).symm
  have h2 : C w * MvPolynomial.coeff m (Ψ (Finsupp.single w 1)) = 1 := by
    have h3 := congrArg (fun p => MvPolynomial.coeff m (Ψ p)) h1
    simp only [map_zsmul, ep, MvPolynomial.coeff_monomial, if_true, MvPolynomial.coeff_smul, smul_eq_mul] at h3
    exact h3.symm
  have h4 : C w = 1 := by
    have := hnn w
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with h | h
    · exact h.1
    · omega
  rw [h4, one_smul] at h1
  exact ⟨w, h1⟩

open GlobalTheory.LocGL.SupportRing in
private theorem occ_of_cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V}
    (hB : HasFiniteLength B) (w : IrrGL k) (hw : clsGL B hB w ≠ 0) :
    N = w.1 ∧ ∀ e : N = w.1, IsSubquotient w.rep (e ▸ B : Representation ℂ (GL (Fin w.1) k) V) := by
  obtain ⟨n, c⟩ := w
  obtain rfl : n = N := by
    by_contra hne
    refine hw ?_
    rw [clsGL, Finsupp.mapDomain_notin_range]
    rintro ⟨c', h'⟩
    exact hne (congrArg Sigma.fst h').symm
  refine ⟨rfl, fun _ => ?_⟩
  exact isSubquotient_of_clsGL_ne hB c.rep.smooth c.rep.irr (by
    have e : IrrGL.of c.rep.ρ c.rep.smooth c.rep.irr = (⟨n, c⟩ : IrrGL k) := IrrGL.of_rep ⟨n, c⟩
    rw [e]
    exact hw)

section

open GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem bas_of_isZSeg {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ} (hS : IsSegmentClass k Z)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    (D : Segment k) (y : IrrGL k) (hy : IsZSeg D y.rep) : bas Ψ y = MvPolynomial.X D := by
  obtain ⟨n, c⟩ := y
  obtain rfl : D.len * D.d = n := hy.deg_eq
  have e : c = Z D := c.cl_rep.symm.trans (IsZSeg.cl_eq hS (π := c.rep) hy)
  rw [← hX D, e]
  rfl

private theorem prod_X_monomial {σ : Type*} {h : ℕ} (Δ : Fin h → σ) (f : Fin h → MvPolynomial σ ℤ)
    (hf : ∀ i, f i = MvPolynomial.X (Δ i)) : ∃ m, ∏ i, f i = MvPolynomial.monomial m (1 : ℤ) := by
  refine Finset.prod_induction _ (fun p => ∃ m, p = MvPolynomial.monomial m (1 : ℤ)) ?_ ⟨0, rfl⟩ fun i _ => ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [MvPolynomial.monomial_mul, one_mul]⟩
  · exact ⟨_, hf i⟩

private theorem occ_prodIrr {h N : ℕ} (z : Fin h → IrrGL k) (hd : ∑ i, (z i).1 = N)
    (hp : HasFiniteLength (prodIrr z hd)) (w : IrrGL k) (hw : clsGL (prodIrr z hd) hp w ≠ 0) :
    ∃ hc : ∑ i, (z i).1 = w.1, IsSubquotient w.rep (prodIrr z hc) := by
  obtain ⟨e, h1⟩ := occ_of_cls hp w hw
  subst e
  exact ⟨hd, h1 rfl⟩

end

open GlobalTheory.LocGL.SupportRing in
theorem UpperTheory.Lit.Full.prodStart :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ : IrrGL k) (h N : ℕ) (Δ : Fin h → Segment k) (z : Fin h → IrrGL k) (hd : ∑ i, (z i).1 = N), ρ.IsCusp → (∀ i, (Δ i).first = ρ) → (∀ i, IsZSeg (Δ i) (z i).rep) → (prodIrr z hd).IsIrreducible := by
  intro hG hBZ hZ k _ _ _ _ ρ h N Δ z hd hρ hf hz
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  obtain ⟨hp, ep⟩ := prodIrr_cls hΨ z hd
  obtain ⟨m, hm⟩ := prod_X_monomial Δ _ fun i => bas_of_isZSeg hS hX _ _ (hz i)
  have hF : ∀ i, FirstIn (z i) {ρ} := fun i => by
    rw [← hf i]
    exact (UpperTheory.Lit.Full.zfirst hG hBZ hZ k (Δ i)).2 (z i) (hz i)
  have key : ∀ w : IrrGL k, clsGL (prodIrr z hd) hp w ≠ 0 →
      HasSupport w.rep (∑ i, (Δ i).ms) ∧ FirstIn w {ρ} := by
    intro w hw
    obtain ⟨hc, h1⟩ := occ_prodIrr z hd hp w hw
    exact ⟨hasSupport_of_isSubquotient_prodIrr hΨ (fun i => (hz i).hasSupport) w.2.rep.irr h1,
      UpperTheory.Lit.Full.firstProd hG hBZ k {ρ} h z w hc hF (jhMult_ne_zero_iff.2 h1)⟩
  have hup : ∀ y ∈ ∑ i, (Δ i).ms, y ∈ up ρ := by
    intro y hy
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hy
    obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hi)
    exact ⟨a, by rw [← ha, hf i]⟩
  obtain ⟨w, h1⟩ := eq_single_of_monomial Ψ _ m (ep.trans hm) (clsGL_nonneg _ hp) fun w x hw hx =>
    (UpperTheory.Lit.Full.redUnique hG hBZ hZ k ρ hρ _ hup w (key w hw).1 (key w hw).2).2 x (key x hx).1 (key x hx).2
  exact GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_of_clsGL_eq_single hp (isSmooth_prodIrr z hd) h1
