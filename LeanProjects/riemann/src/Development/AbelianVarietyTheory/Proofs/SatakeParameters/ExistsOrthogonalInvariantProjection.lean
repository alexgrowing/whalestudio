import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProjectiveChartAffineCover
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

theorem mem_germ_range_of_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  intro d Z _ p _ inst hinst φ _ _ hgen I hI h y hy
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hsc : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    subst hinst; intro r; rfl
  set U : Z.Opens := I.inf fun i => φ ⁻¹ᵁ chart d i with hU
  have hUa : IsAffineOpen U := (GlobalTheory.T.projective_chart_affine_cover d Z φ).2 I hI
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hUa
  have halg : ∀ b, algebraMap Γ(Z, U) Z.functionField b = (Z.presheaf.germ U (genericPoint Z) h).hom b := fun _ => rfl
  haveI : IsIntegrallyClosed Γ(Z, U) := by
    have hs := p.smooth_appLE (U := ⊤) (isAffineOpen_top _) hUa (by simp)
    letI := (p.appLE ⊤ U (by simp)).hom.toAlgebra
    haveI : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    haveI : IsDomain Γ(Sp ℂ, ⊤) := e.injective.isDomain (e : Γ(Sp ℂ, ⊤) →+* ℂ)
    haveI : IsIntegrallyClosed Γ(Sp ℂ, ⊤) := IsIntegrallyClosed.of_equiv e.symm
    exact isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)
  have hgerm : ∀ a ∈ rA ℂ (crd φ) I, ∃ g : Γ(Z, U),
      (Z.presheaf.germ U (genericPoint Z) h).hom g = ((a : fld φ) : Z.functionField) := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, j, rfl⟩ := hx
      have hle : U ≤ φ ⁻¹ᵁ chart d i := Finset.inf_le hi
      refine ⟨Z.presheaf.map (homOfLE hle).op (φ.app (chart d i) (ratioSec d i j)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      have hr := (GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d Z φ 0 i j (hgen 0) (hgen i)).2
      simp only [IntermediateField.coe_div, crd_val]
      rw [← hr, rat, dif_pos (hgen i)]
    | algebraMap r =>
      refine ⟨Z.presheaf.map (homOfLE le_top).op (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      exact (hsc r).symm
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g + g', by rw [map_add, hg, hg']; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g * g', by rw [map_mul, hg, hg']; rfl⟩
  have hy' : IsIntegral (rA ℂ (crd φ) I) y := hy
  have hB : IsIntegral Γ(Z, U) y := by
    obtain ⟨q, hq, hqy⟩ := hy'
    have hl : q.map (algebraMap (rA ℂ (crd φ) I) Z.functionField) ∈
        Polynomial.lifts (algebraMap Γ(Z, U) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨g, hg⟩ := hgerm _ (q.coeff n).2
      exact ⟨g, by rw [halg, hg]; rfl⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hq.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, hqy]
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hB
  exact ⟨b, hb⟩

end GlobalTheory.PD.XCover
