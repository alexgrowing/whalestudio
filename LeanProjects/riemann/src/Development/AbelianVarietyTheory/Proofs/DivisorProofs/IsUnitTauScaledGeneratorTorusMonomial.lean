import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.ScaleTorus

theorem unitOn_mul' {R : Type} [CommRing R] (x y : Rˣ) : unitOn (x * y) = unitOn x * unitOn y := by
  apply Units.ext
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (x : R) (y : R)

theorem isUnitTau_scaleGen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C N s ε τ₀ hs hε hτ u hu a b
  obtain ⟨hgen, k, hk, hval⟩ := hτ a b
  set w : Rˣ := ∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) with hw
  let w' : (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom w
  have hw' : (w' : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s (.inr k)) ^
      ((l.M' : ℤ) • (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b := by
    simp only [w', hw, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      LinearMap.smul_apply, smul_eq_mul, ← hu]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen _ _ hgen, k * w'⁻¹, ?_, fun zz J hJ => ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ w'.ne_zero, hk, hw']
    refine (finSumFinEquiv.symm.prod_comp fun k => algebraMap R (FractionRing R) (s k) ^
      ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [hs, hε]
  · have e₁ : val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen (unitOn w) (τ₀ a b)) (toUnit (TK R)).left zz J =
        gm (toUnit (TK R)).left zz ⊤ (unitOn w) * val (τ₀ a b) (toUnit (TK R)).left zz J :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ zz le_top (hJ.mem _ _) _) rfl)
    have e₂ : gm (toUnit (TK R)).left zz ⊤ (unitOn w) = gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      have e : (toUnit (TK R)).left = spMap (algebraMap R (FractionRing R)) := by simp
      rw [e]
      exact SepBModel.gm_spMap _ zz w
    have e₃ : gm (𝟙 (TK R).left) zz ⊤ (unitOn k) =
        gm (𝟙 (TK R).left) zz ⊤ (unitOn (k * w'⁻¹)) * gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      refine Eq.trans ?_ (map_mul _ _ _)
      refine congrArg _ (Eq.trans ?_ (unitOn_mul' _ _))
      rw [inv_mul_cancel_right]
    refine (hval zz J hJ).trans (Eq.trans ?_ (congrArg _ e₁.symm))
    rw [e₂, ← _root_.mul_assoc, ← e₃]

end GlobalTheory.UCanon.ScaleTorus
