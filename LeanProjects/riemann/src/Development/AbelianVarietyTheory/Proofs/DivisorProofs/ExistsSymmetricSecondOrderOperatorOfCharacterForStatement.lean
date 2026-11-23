import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricSecondOrderOperatorOfCharacterFor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
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
theorem _root_.GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  first | exact @GlobalTheory.HeatMod.TorTensor.exists_quad | exact GlobalTheory.HeatMod.TorTensor.exists_quad | (intros; apply GlobalTheory.HeatMod.TorTensor.exists_quad <;> assumption)
