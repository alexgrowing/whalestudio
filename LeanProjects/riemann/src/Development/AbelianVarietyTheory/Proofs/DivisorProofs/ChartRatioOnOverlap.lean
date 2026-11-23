import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem unit_ratio_norm_sub_le_max {p : ℕ} [Fact p.Prime] (x y : ℂ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem unit_ratio_close : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  intro p _ X Xw K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 h1 h2 H1 H2 χ1 χ2 hχ1 hχ2 φ hφ ψ hψ
  have e1 : spMap (φ.comp a1) ≫ ξ1 = spMap φ ≫ w := by rw [← sp_sp, h1]
  have e2 : spMap (φ.comp a2) ≫ ξ2 = spMap φ ≫ w := by rw [← sp_sp, h2]
  have hψ1 : (ψ.comp χ1).comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a1) := by
    rw [RingHom.comp_assoc, hχ1, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  have hψ2 : (ψ.comp χ2).comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a2) := by
    rw [RingHom.comp_assoc, hχ2, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  obtain ⟨κ, hκ⟩ := hK _ hφ
  have k1 := H1 (φ.comp a1) (by rw [e1]; exact hφ) (ψ.comp χ1) hψ1 κ (by rw [e1]; exact hκ)
  have k2 := H2 (φ.comp a2) (by rw [e2]; exact hφ) (ψ.comp χ2) hψ2 κ (by rw [e2]; exact hκ)
  simp only [RingHom.comp_apply] at k1 k2
  set a := ψ (χ1 (c1 : Localization.Away (p : R1)))
  set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
  have hab : ‖a - b‖ < ‖κ‖ := by
    have : a - b = (a - κ) - (b - κ) := by ring
    rw [this]
    exact lt_of_le_of_lt (unit_ratio_norm_sub_le_max _ _) (max_lt k1 k2)
  have hb : ‖b‖ = ‖κ‖ := by
    apply le_antisymm
    · have : b = (b - κ) + κ := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k2.le le_rfl)
    · have : κ = b - (b - κ) := by ring
      calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
        _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
        _ ≤ ‖b‖ := by
            refine max_le le_rfl ?_
            by_contra hc
            push_neg at hc
            have h3 : ‖κ‖ ≤ max ‖b‖ ‖b - κ‖ := by
              calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
                _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
            rw [max_eq_right hc.le] at h3
            linarith
  rw [hb]; exact hab

end GlobalTheory.FlatModel
