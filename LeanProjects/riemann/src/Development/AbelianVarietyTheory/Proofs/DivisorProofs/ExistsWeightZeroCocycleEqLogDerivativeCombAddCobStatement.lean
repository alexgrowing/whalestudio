import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  first | exact @GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob | exact GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob | (intros; apply GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob <;> assumption)
