import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt

namespace PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.CarriedPot

theorem isPotential_tAtlas_pullback : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P →
      IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  intro e X X' _ _ A h P hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hs := hP.1 (h.symm x) j
    have e₁ : (P.pullback h.symm h.symm.continuous).φ x ∘ ((tAtlas A h).chart j).symm =
        P.φ (h.symm x) ∘ (A.chart j).symm := funext fun w => by
      simp only [Function.comp_apply, tAtlas_symm, LocPot.pullback, Homeomorph.symm_apply_apply]
    have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹'
          (P.pullback h.symm h.symm.continuous).U x =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U (h.symm x) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm, LocPot.pullback,
        Homeomorph.symm_apply_apply]
    rw [e₁, e₂]
    exact hs
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 (h.symm x) (h.symm x') (h.symm y) hy
    refine ⟨h.symm ⁻¹' W, hW.preimage h.symm.continuous, hyW, G ∘ h.symm, fun j => ?_, fun z hz => ?_⟩
    · have hs := hG j
      have e₁ : (G ∘ h.symm) ∘ ((tAtlas A h).chart j).symm = G ∘ (A.chart j).symm := funext fun w => by
        simp only [Function.comp_apply, tAtlas_symm, Homeomorph.symm_apply_apply]
      have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' W) =
          (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm,
          Homeomorph.symm_apply_apply]
      rw [e₁, e₂]
      exact hs
    · exact hd (h.symm z) hz

end GlobalTheory.CompanionTheory.CarriedPot

end

end PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.isPotential_transport_homeomorph : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P → IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  first | exact @PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | exact PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | (intros; apply PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback <;> assumption)

end
