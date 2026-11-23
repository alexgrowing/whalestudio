import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.Gauge

theorem gU_transition : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (p p' : h₁.J × (Fin 2 → L.ι)) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p ⊓ GlobalTheory.Heat.Gauge.W m h₁ p' → pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p').val O = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he p p' O hO
  have hWp : O ≤ W m h₁ p := hO.trans inf_le_left
  have hWp' : O ≤ W m h₁ p' := hO.trans inf_le_right
  have gv : ∀ q, O ≤ W m h₁ q → rsT (gU m h₁ e q).val O =
      rsT (e.s q.2).val O * pbT m₁ (L.g (q.2 1) (h₁.j q.1)).val O := by
    intro q hq
    rw [gU, Units.val_mul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.AdjDlog.val_res_pullU m₁ (W_le_m₁ m h₁ q),
      GlobalTheory.KS.rsT_pbT m₁ (W_le_m₁ m h₁ q) hq]
    have a : rsT (res (W_le_wchart m h₁ q) (e.s q.2)).val O = rsT (e.s q.2).val O :=
      (congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res (W_le_wchart m h₁ q) (e.s q.2))).trans
        (GlobalTheory.KS.rsT_rsT (W_le_wchart m h₁ q) hq _)
    exact congrArg (· * _) a
  have hj : O ≤ LB.wchart L ![m, m₁] p.2 ⊓ LB.wchart L ![m, m₁] p'.2 :=
    le_inf (hWp.trans (W_le_wchart m h₁ p)) (hWp'.trans (W_le_wchart m h₁ p'))
  have hj' : O ≤ (LB.LinComb L ![m, m₁] ![1, -1]).U p.2 ⊓ (LB.LinComb L ![m, m₁] ![1, -1]).U p'.2 := hj
  have g1 : rsT (e.s p.2).val O = (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O := by
    have g0 := congrArg (fun u => (res hj' u).val) (he p.2 p'.2)
    simp only [map_mul, Units.val_mul, GlobalTheory.KS.AdjDlog.res_res'] at g0
    rw [GlobalTheory.KS.AdjDlog.val_res hj']
    simpa only [GlobalTheory.KS.AdjDlog.val_res] using g0
  have le : ∀ k : Fin 2, O ≤ (![m, m₁] k) ⁻¹ᵁ (L.U (p.2 k) ⊓ L.U (p'.2 k)) := fun k =>
    le_inf ((hj.trans inf_le_left).trans (LB.wchart_le L _ _ k)) ((hj.trans inf_le_right).trans (LB.wchart_le L _ _ k))
  have ec : res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2) =
      ∏ k, res (le k) (pullU _ _ (L.g (p.2 k) (p'.2 k))) ^ (![(1 : ℤ), -1] k) := by
    refine (map_prod (res hj') _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow (res hj') _ _).trans ?_)
    exact congrArg (fun u => u ^ (![(1 : ℤ), -1] k)) (GlobalTheory.KS.AdjDlog.res_res' _ hj' _)
  have v0 : (res (le 0) (pullU (![m, m₁] 0) _ (L.g (p.2 0) (p'.2 0)))).val = pbT m (L.g (p.2 0) (p'.2 0)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 0) _
  have v1 : (res (le 1) (pullU (![m, m₁] 1) _ (L.g (p.2 1) (p'.2 1)))).val = pbT m₁ (L.g (p.2 1) (p'.2 1)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 1) _
  have hv : (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * pbT m₁ (L.g (p.2 1) (p'.2 1)).val O =
      pbT m (L.g (p.2 0) (p'.2 0)).val O := by
    rw [ec, Fin.prod_univ_two, ← v0, ← v1]
    rw [show (![(1 : ℤ), -1] 0) = 1 from rfl, show (![(1 : ℤ), -1] 1) = -1 from rfl, zpow_one, zpow_neg_one,
      ← Units.val_mul, inv_mul_cancel_right]
  have m1p := hWp.trans (W_le_m₁ m h₁ p)
  have m1p' := hWp'.trans (W_le_m₁ m h₁ p')
  have coc1 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (h₁.j p.1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p hy).2⟩, (m1p' hy).2⟩)
  have coc2 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (p'.2 1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p' hy).1⟩, (m1p' hy).2⟩)
  rw [gv p hWp, gv p' hWp']
  linear_combination -(rsT (e.s p'.2).val O * pbT m₁ (L.g (p'.2 1) (h₁.j p'.1)).val O) * hv +
    ((res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O) * coc2 -
    pbT m₁ (L.g (p.2 1) (h₁.j p'.1)).val O * g1 - rsT (e.s p.2).val O * coc1

end GlobalTheory.Heat.Gauge
