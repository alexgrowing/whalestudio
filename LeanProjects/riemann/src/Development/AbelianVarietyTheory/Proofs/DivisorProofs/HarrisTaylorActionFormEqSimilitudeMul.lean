import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actG_form_eq_sim : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  intro p _ D G L g v w
  set y : (AfP p ⊗[ℚ] G.C)ˣ := (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 with hy
  set c : AfP p := (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) with hc
  have hmem : (y : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := mem_uGroup.1 g.2
  have hsy : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop * (y : AfP p ⊗[ℚ] G.C) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
    have h1 : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
        ((y⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
      rw [← hmem, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [h1, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hact : ∀ u : AfP p ⊗[ℚ] VQ D, L.actG g u = actOn L.rep (AfP p) (y : AfP p ⊗[ℚ] G.C) u := fun u => rfl
  rw [hact, hact, GlobalTheory.LKGeo.adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, hsy, AlgHom.commutes,
    Module.algebraMap_end_apply, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.LKGeo
