import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_pow_eq_integral_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (M : RigLB G) (B : Scheme.{0}) (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (t : Sp (FractionRing V) ⟶ B) (ψ : pullback G.hom (jK V) ⟶ P.A.left), IsGrpPullback ((Over.pullback (jK V)).obj G) P.A t ψ → ∀ (w : LB.Iso (M.L.pull (pullback.fst G.hom (jK V))) (P.L.pull ψ)), w.IsGen → ∀ n : ℕ, ∃ lam : FractionRing V, lam ≠ 0 ∧ ∀ (z : baseOver B ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver B).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))), IsTorsFrame P rig n z τ → ∀ (h : baseOver (Sp V) ⟶ G) (x : Sp (FractionRing V) ⟶ pullback G.hom (jK V)), x ≫ pullback.fst G.hom (jK V) = jK V ≫ h.left → x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → x ≫ ψ = t ≫ z.left → ∀ (i : M.L.ι) (k : P.L.ι), ⊤ ≤ h.left ⁻¹ᵁ M.L.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ P.L.U k → ∃ v : Vˣ, valR (X := (baseOver B).left) t _ (τ.s (fun _ => k)).val ^ (n ^ 2) = (lam * valR x _ (w.s (fun _ => k, fun _ => i)).val) ^ (n ^ 2) * algebraMap V (FractionRing V) v := by
  first | exact @GlobalTheory.TorsFrameInt.torsFrame_pow_eq | exact GlobalTheory.TorsFrameInt.torsFrame_pow_eq | (intros; apply GlobalTheory.TorsFrameInt.torsFrame_pow_eq <;> assumption)
