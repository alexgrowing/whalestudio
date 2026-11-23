import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem unitChartAt_of_dvd : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  intro p n _ X X' π Xw K R _ ξ J Q u hC hT R' _ χ g x' hχ hx' hχπ _hD hcase
  have hcomp : ∀ φ : R' →+* 𝓞_ℂ_[p], (spMap φ ≫ χ) ≫ π = spMap (φ.comp g) ≫ ξ := by
    intro φ; rw [Category.assoc, hχπ, sp_sp]
  have hm : ∀ x : 𝓞_ℂ_[p], ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    have this : (Valued.v (x : ℂ_[p]) : NNReal) ≤ 1 := x.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have htest : ∀ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ) →
      IsTest p Xw (spMap (φ.comp g) ≫ ξ) := by
    intro φ h; rw [← hcomp]; exact hT _ h
  rcases hcase with ⟨k, hk, hkp⟩ | hall
  · have hunit : IsUnit ((algebraMap R' (Localization.Away (p : R'))).comp g ((p : R) * Q k)) := by
      obtain ⟨d, hd⟩ := hkp
      have h1 : IsUnit (algebraMap R' (Localization.Away (p : R')) ((p : R') ^ (n + 1))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (p : R')).pow _
      refine isUnit_of_dvd_unit ⟨algebraMap R' _ d, ?_⟩ h1
      simp only [RingHom.comp_apply, map_mul, map_natCast]
      rw [pow_succ', hd, map_mul, map_mul, map_natCast]; ring
    let L := IsLocalization.Away.lift (S := Localization.Away ((p : R) * Q k)) ((p : R) * Q k) hunit
    refine ⟨R', inferInstance, χ, Units.map L.toMonoidHom (u k), hχ, hx', ?_⟩
    intro φ hφ ψ hψ κ hκ
    obtain ⟨⟨j, hj⟩, hcl⟩ := hC (φ.comp g) (htest φ hφ)
    have hkbig : (p : ℝ)⁻¹ ^ n < ‖((φ.comp g) (Q k) : ℂ_[p])‖ := by
      refine hj.trans_le ?_
      obtain ⟨d, hd⟩ := hk j
      have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((φ.comp g) (Q k) : ℂ_[p]) * (φ d : ℂ_[p]) := by
        rw [RingHom.comp_apply, hd, map_mul]; rfl
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hm _)
    have hcompat : (ψ.comp L).comp (algebraMap R (Localization.Away ((p : R) * Q k))) =
        (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp g) := by
      ext r
      have := RingHom.congr_fun hψ (g r)
      simp only [RingHom.comp_apply] at this ⊢
      rw [← this]
      congr 1
      exact IsLocalization.lift_eq _ r
    have hκ' : κ ∈ K (spMap (φ.comp g) ≫ ξ) := by rw [← hcomp]; exact hκ
    exact hcl k hkbig (ψ.comp L) hcompat κ hκ'
  · refine ⟨R', inferInstance, χ, 1, hχ, hx', ?_⟩
    intro φ hφ
    exfalso
    obtain ⟨⟨j, hj⟩, -⟩ := hC (φ.comp g) (htest φ hφ)
    obtain ⟨d, hd⟩ := hall j
    have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = (p : ℂ_[p]) ^ n * (φ d : ℂ_[p]) := by
      rw [RingHom.comp_apply, hd, map_mul, map_pow, map_natCast]; push_cast; rfl
    rw [e, norm_mul, norm_pow, hpn] at hj
    have := mul_le_of_le_one_right (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg p) : (0:ℝ) ≤ (p : ℝ)⁻¹) n) (hm (φ d))
    linarith

end GlobalTheory.FlatModel
