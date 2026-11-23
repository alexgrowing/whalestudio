import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRatioOnOverlapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementOfDvrTestPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenAffineIntegrallyClosedDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitOfTestPointEstimateStatement

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

theorem exists_unit_ratio_of_close : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
  intro F _ _ V _ p _ hp hD X s Xw hXi hXn hproj hflat hXw hne K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 hξ1 hξ2 hw e1 e2 hc1 hc2
  classical
  have hlft : LocallyOfFiniteType s := GlobalTheory.T.locallyOfFiniteType_of_isProjOver V X s hproj
  have hu1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : R1)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  have hu2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : R2)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  let χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R1) hu1
  let χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R2) hu2
  have hχ1 : χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hχ2 : χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hcl := GlobalTheory.T.chart_ratio_on_overlap p X Xw K hK R1 R2 A ξ1 ξ2 w c1 c2 a1 a2 e1 e2 hc1 hc2 χ1 χ2 hχ1 hχ2
  let r : (Localization.Away (p : A))ˣ := Units.map (χ1 : _ →* _) c1 * (Units.map (χ2 : _ →* _) c2)⁻¹
  have hr : (r : Localization.Away (p : A)) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
    have h0 : r * Units.map (χ2 : _ →* _) c2 = Units.map (χ1 : _ →* _) c1 := by simp [r]
    have h0' := congrArg Units.val h0
    simpa using h0'
  have hnorm : ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p],
      ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
      ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 ∧ ‖ψ (r : Localization.Away (p : A))‖ = 1 ∧
        ‖ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A))‖ = 1 := by
    intro φ hφ ψ hψ
    have h := hcl φ hφ ψ hψ
    set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
    have hb : b ≠ 0 := ((c2.isUnit.map χ2).map ψ).ne_zero
    have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
    have hrb : ψ (r : Localization.Away (p : A)) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) := by
      rw [← map_mul, hr]
    have h1 : ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 := by
      have : (ψ (r : Localization.Away (p : A)) - 1) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) - b := by
        rw [sub_mul, hrb, _root_.one_mul]
      have h2 : ‖ψ (r : Localization.Away (p : A)) - 1‖ * ‖b‖ < 1 * ‖b‖ := by
        rw [← norm_mul, this, _root_.one_mul]; exact h
      exact lt_of_mul_lt_mul_right h2 hbn.le
    have h3 : ‖ψ (r : Localization.Away (p : A))‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℂ_[p])) (y := ψ (r : Localization.Away (p : A)) - 1) (by rw [norm_one]; exact h1.ne')
      rw [add_sub_cancel, norm_one, max_eq_left h1.le] at this
      exact this
    refine ⟨h1, h3, ?_⟩
    have h4 : ψ (r : Localization.Away (p : A)) * ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h5 := congrArg norm h4
    rw [norm_mul, h3, _root_.one_mul, norm_one] at h5
    exact h5
  have hfin : ∀ χ1' : Localization.Away (p : R1) →+* Localization.Away (p : A), ∀ χ2' : Localization.Away (p : R2) →+* Localization.Away (p : A),
      χ1'.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2'.comp (algebraMap R2 _) = (algebraMap A _).comp a2 →
      χ1' = χ1 ∧ χ2' = χ2 := fun χ1' χ2' h1 h2 =>
    ⟨IsLocalization.ringHom_ext (Submonoid.powers (p : R1)) (h1.trans hχ1.symm),
      IsLocalization.ringHom_ext (Submonoid.powers (p : R2)) (h2.trans hχ2.symm)⟩
  by_cases hA : Nonempty (Sp A)
  swap
  · have hsub : Subsingleton A := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact hA inferInstance
    have hsubL : Subsingleton (Localization.Away (p : A)) := by
      refine ⟨fun x y => ?_⟩
      rw [← _root_.mul_one x, ← _root_.mul_one y, ← map_one (algebraMap A (Localization.Away (p : A))), Subsingleton.elim (1 : A) 0, map_zero, mul_zero, mul_zero]
    refine ⟨1, by simp, fun χ1' χ2' _ _ => Subsingleton.elim _ _⟩
  obtain ⟨hdom, hic, alg, hft, hinjV, e, he0, htest⟩ := GlobalTheory.T.open_affine_integrally_closed_domain F V p hp X s Xw hXi hXn hflat hlft hXw hne A w hw hA
  have hbdd : ∀ x : (Localization.Away (p : A))ˣ, (x = r ∨ x = r⁻¹) → ∃ a : A, algebraMap A _ a = (x : Localization.Away (p : A)) := by
    intro x hx
    refine GlobalTheory.T.element_of_dvr_test_points F V p hp A hinjV e he0 _ fun T kO φ hT hkO hφe ψ hψ => ?_
    have := hnorm (kO.comp φ) (htest T kO φ hT hkO hφe) ψ hψ
    rcases hx with rfl | rfl
    · exact this.2.1.le
    · exact this.2.2.le
  obtain ⟨a, ha⟩ := hbdd r (Or.inl rfl)
  obtain ⟨b, hb⟩ := hbdd r⁻¹ (Or.inr rfl)
  have hp0 : (p : A) ≠ 0 := by
    intro h0
    have : algebraMap V A (p : V) = algebraMap V A 0 := by rw [map_natCast, map_zero, h0]
    have h1 := hinjV this
    have h2 := congrArg (fun x : V => (x : F)) h1
    simp at h2
    exact (Fact.out : p.Prime).ne_zero h2
  have hinjL : Function.Injective (algebraMap A (Localization.Away (p : A))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  have hab : a * b = 1 := hinjL (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  let u : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨u, ?_, fun χ1' χ2' h1 h2 => ?_⟩
  · refine GlobalTheory.T.unit_of_test_point_estimate F V p hp hD X s Xw hXi hflat hlft hXw hne A w hw a fun φ hφ => ?_
    have hpu : IsUnit (((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) (p : A)) := by
      rw [map_natCast]
      exact IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let ψ : Localization.Away (p : A) →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hpu
    have hψ : ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ := IsLocalization.lift_comp _
    have := (hnorm φ hφ ψ hψ).1
    rw [← ha] at this
    have e3 : ψ (algebraMap A _ a) = (φ a : ℂ_[p]) := RingHom.congr_fun hψ a
    rw [e3] at this
    exact this
  · obtain ⟨rfl, rfl⟩ := hfin χ1' χ2' h1 h2
    change algebraMap A _ a * _ = _
    rw [ha, hr]

end GlobalTheory.FlatModel
