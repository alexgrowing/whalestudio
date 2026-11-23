import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.ord_fnPull_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  intro k _ X Y _ _ p s _ hs E' E h g
  let φ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring fun a => (h _).1 a.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hs.1 (congrArg Subtype.val e)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hs.2 (b : Y.functionField)
    exact ⟨⟨a, (h a).2 (ha ▸ b.2)⟩, Subtype.ext ha⟩
  let e : E.ring ≃+* E'.ring := RingEquiv.ofBijective φ hφ
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, u, eg⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := Y.functionField) (ht.map e)
    (Units.map e.toMonoidHom u) m
  rw [← eg, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have eg' : ((fnPull s g : Y.functionFieldˣ) : Y.functionField) =
      algebraMap E'.ring Y.functionField (Units.map e.toMonoidHom u : E'.ringˣ) *
        algebraMap E'.ring Y.functionField (e t) ^ m := by
    change functionFieldMap s (g : X.functionField) = _
    rw [eg, map_mul, map_zpow₀]
    rfl
  rw [← eg', ordTop_vw_of_ne_zero _ (fnPull s g).ne_zero, WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.Discrepancy
