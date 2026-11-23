import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValClosure

theorem vV_eq_of_hasVal {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {x : FractionRing V} {n : ℤ} (h : ReciprocityTheory.ChartRestriction.G.DVR.HasVal ϖ x n) : vV V x = n := by
  obtain ⟨u, rfl⟩ := h
  have h1 : valV V (algebraMap V (FractionRing V) ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  have hle : ∀ w : V, valV V (algebraMap V (FractionRing V) w) ≤ 1 := fun w =>
    HeightOneSpectrum.valuation_le_one _ w
  have h2 : valV V (algebraMap V (FractionRing V) (u : V)) = 1 := by
    refine le_antisymm (hle _) ?_
    have h3 : valV V (algebraMap V (FractionRing V) (u : V)) *
        valV V (algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ valV V (algebraMap V (FractionRing V) (u : V)) * 1 := mul_le_mul' le_rfl (hle _)
      _ = _ := _root_.mul_one _
  rw [vV, map_mul, h2, _root_.mul_one, map_zpow₀, h1, WithZero.log_zpow, WithZero.log_exp]
  simp

theorem exists_valuation_closure : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v ∧ ∀ x : FractionRing V, x ≠ 0 → v (algebraMap _ _ x) = (((vV V x : ℤ) : ℚ) : WithTop ℚ) := by
  intro V _ _ _ ϖ hϖ
  obtain ⟨v, hv⟩ := GlobalTheory.exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure (FractionRing V))
  refine ⟨v, hv, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
  rw [vV_eq_of_hasVal hϖ hn]
  exact hv x n hn

end GlobalTheory.ValClosure
