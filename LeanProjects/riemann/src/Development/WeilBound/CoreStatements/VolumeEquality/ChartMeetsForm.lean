import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique

noncomputable section

namespace SheetDecomposition.ChartForm

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ (V : X.Opens) (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V) (hg : genPt ξ ∈ V) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f) := by
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

theorem exists_form {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (U : X.Opens) (hU : genPt ξ ∈ U) :
    ∃ g : MvPolynomial (Σ k, J k) ℤ, g ∉ mCoordIdeal y ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ),
      genPt ξ ⤳ centre z → CoordsAt ξ y z w → aeval w g ≠ 0 → centre z ∈ U := by
  classical
  have hξ := T.gen
  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨V, hV, hmem⟩ := T.affine c hc.1
  have hgV : genPt ξ ∈ V := (hmem _).2 ⟨specializes_rfl, hc⟩
  obtain ⟨f, hfU, hgf⟩ := hV.exists_basicOpen_le ⟨genPt ξ, hU⟩ hgV
  obtain ⟨a, ha⟩ : ∃ a : Ω, a = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hgV f) := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    have h1 := (X.mem_basicOpen f (genPt ξ) hgV).1 hgf
    rw [ha]
    exact (h1.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  have haA := (T.ring c hc.1 a).2 fun p hp =>
    ⟨_, (genMap_germ V f p ((hmem _).2 ⟨p.2, hp⟩) hgV).trans ha.symm⟩
  let t : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  have h1 : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      (aeval t : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Ω).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩
    change aeval t (∏ k, MvPolynomial.X ⟨k, j k⟩) = _
    rw [map_prod]
    simp only [aeval_X, t]
    exact Finset.prod_div_distrib _ _
  obtain ⟨F₀, hF₀⟩ := h1 haA
  have hF₀' : aeval t F₀ = a := hF₀
  obtain ⟨F, d, hF⟩ := exists_homog c F₀
  refine ⟨F * ∏ k, MvPolynomial.X ⟨k, c k⟩, fun h => ?_, fun z w hz hw hne => ?_⟩
  · have h2 := hF (MvPolynomial K Ω) (fun p => C (y p) * MvPolynomial.X p.1)
      (fun p => C (y p / y ⟨p.1, c p.1⟩)) (fun k => C (y ⟨k, c k⟩) * MvPolynomial.X k)
      (fun k => by simp [div_self (hy k)])
      (fun p => by rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hy p.1)])
    have h3 : aeval (fun p : Σ k, J k => (C (y p) * MvPolynomial.X p.1 : MvPolynomial K Ω))
      (F * ∏ k, MvPolynomial.X ⟨k, c k⟩) = 0 := h
    have h4 := map_aeval_int (C : Ω →+* MvPolynomial K Ω) t F₀
    rw [map_mul, h2, map_prod, ← h4, hF₀'] at h3
    have h5 : ∀ k, (C (y ⟨k, c k⟩) * MvPolynomial.X k : MvPolynomial K Ω) ≠ 0 := fun k =>
      mul_ne_zero (by simpa using hy k) (X_ne_zero k)
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero d (h5 k)) (by simpa using ha0))
      (Finset.prod_ne_zero_iff.2 fun k _ => ?_) h3
    rw [aeval_X]
    exact h5 k
  · rw [map_mul, map_prod] at hne
    have hw0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
      have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne) k (Finset.mem_univ k)
      rwa [aeval_X] at this
    have hr : ∀ p : Σ k, J k, ∃ r : ℂ, ValAt ξ z (t p) r ∧ w p = r * w ⟨p.1, c p.1⟩ := fun p =>
      (hw.2 p.1 (c p.1) (hw0 p.1).isUnit).2 p.2
    choose s hs1 hs2 using hr
    have hs3 : ∀ k, s ⟨k, c k⟩ = 1 := fun k => by
      have h6 : w ⟨k, c k⟩ = s ⟨k, c k⟩ * w ⟨k, c k⟩ := hs2 ⟨k, c k⟩
      exact (mul_right_cancel₀ (hw0 k) (h6.symm.trans (one_mul _).symm))
    have h7 := hF ℂ w s (fun k => w ⟨k, c k⟩) hs3 hs2
    have h8 : aeval s F₀ ≠ 0 := right_ne_zero_of_mul (h7 ▸ left_ne_zero_of_mul hne)
    obtain ⟨φ, hφ, _⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z hz hξ
    have hreg : ∀ p, t p ∈ regAt ξ ⟨centre z, hz⟩ := fun p => ((hφ _ _).1 (hs1 p)).1
    have hφs : ∀ p, φ ⟨t p, hreg p⟩ = s p := fun p => ((hφ _ _).1 (hs1 p)).2
    have hzc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
      refine ⟨hc.1, fun j => ?_⟩
      have h9 : (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) = ∏ k, t ⟨k, j k⟩ := (Finset.prod_div_distrib _ _).symm
      change (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c k⟩) ∈ _
      rw [h9]
      exact prod_mem fun k _ => hreg _
    have hzV : centre z ∈ V := (hmem _).2 ⟨hz, hzc⟩
    let b : regAt ξ ⟨centre z, hz⟩ := aeval (fun p => (⟨t p, hreg p⟩ : regAt ξ ⟨centre z, hz⟩)) F₀
    have hb : (b : Ω) = a := by
      rw [← hF₀']
      exact map_aeval_int (regAt ξ ⟨centre z, hz⟩).subtype _ F₀
    have hφb : φ b = aeval s F₀ := by
      rw [map_aeval_int]
      simp only [hφs]
    have hval : ValAt ξ z a (aeval s F₀) := by
      rw [← hb, ← hφb]
      exact (hφ _ _).2 ⟨b.2, rfl⟩
    obtain ⟨_, σ, e1, e2⟩ := hval
    have e3 : σ = X.presheaf.germ V (centre z) hzV f :=
      hξ.inj ⟨centre z, hz⟩ (e1.trans (ha.trans (genMap_germ V f ⟨centre z, hz⟩ hzV hgV).symm))
    have e4 : IsUnit ((Scheme.stalkClosedPointTo z).hom σ) := by
      rw [e2]
      exact h8.isUnit
    have e5 : IsUnit σ := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit σ e4
    exact hfU ((X.mem_basicOpen f (centre z) hzV).2 (e3 ▸ e5))

end SheetDecomposition.ChartForm
