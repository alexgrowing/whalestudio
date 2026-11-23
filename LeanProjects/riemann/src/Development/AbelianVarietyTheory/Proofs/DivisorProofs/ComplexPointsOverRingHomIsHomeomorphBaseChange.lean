import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isHomeomorph_bcPt (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0})
    (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) :
    IsHomeomorph (bcPt hp.w τ) := by
  let E : CxPts q τ ≃ CxPts p (τ.comp ρ) := Equiv.ofBijective (bcPt hp.w τ) (CxPts.bijective_bcMap hp τ)
  have hm : ∀ z, (bcPt hp.w τ z).1 = z.1 ≫ j := fun _ => rfl
  have hE : ∀ y, bcPt hp.w τ (E.symm y) = y := E.apply_symm_apply
  have hc : Continuous E.symm := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨U, hyU⟩ := CxPts.exists_mem_ptsIn (iSup_affineOpens_eq_top X) y
    have hU : IsAffineOpen U.1 := U.2
    have hW : IsAffineOpen (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := by
      rw [show j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤ = j ⁻¹ᵁ U.1 from inf_top_eq _]
      exact GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback hp hU
    have hin : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := fun w hw =>
      mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (by rw [hE]; exact hw), mem_ptsIn_top⟩
    have hnb : ptsIn p (τ.comp ρ) U.1 ∈ 𝓝 y := (isOpen_ptsIn _).mem_nhds hyU
    have hev : ∀ᶠ w in 𝓝 y, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := eventually_of_mem hnb hin
    letI := ρ.toAlgebra
    have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout (isPushout_sections p q j hp U.1 hU)
    refine tendsto_subtype_rng.2 ((Points.tendsto_iff_of_generators hW (hin y hyU) hgen).2 ⟨hev, ?_⟩)
    rintro f (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, ev p (τ.comp ρ) U.1 a w =
          valR (E.symm w).1 _ ((j.appLE U.1 (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom a) := fun w hw => by
        have := CxPts.ev_appLE_of_comp hm inf_le_left a (hin w hw)
        rw [hE] at this
        exact this.symm
      have h := ((continuousOn_ev a).continuousAt hnb).tendsto
      rw [e y hyU] at h
      exact h.congr' (eventually_of_mem hnb e)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, τ b =
          valR (E.symm w).1 _ (algX q (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) b) := fun w hw => (ev_algX (hin w hw) b).symm
      have h : Tendsto (fun _ : CxPts p (τ.comp ρ) => τ b) (𝓝 y) (𝓝 (τ b)) := tendsto_const_nhds
      have h' := h.congr' (eventually_of_mem hnb e)
      rw [e y hyU] at h'
      exact h'
  exact (Homeomorph.mk E (continuous_bcPt hp.w τ) hc).isHomeomorph

end GlobalTheory.Mix
