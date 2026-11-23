import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorsDifferenceGlobal
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
theorem _root_.GlobalTheory.T.torusInvariant_heatOperators_difference_global : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (e : Fin n → R) (π π' : R), (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) ∧ ∀ (i : h.J) (i' : h'.J) (Wo : Y.H.left.Opens), Wo ≤ h.W i ⊓ h'.W i' → (∀ f, h.d i Wo f - h'.d i' Wo f = ∑ a, constFn Y.H.hom Wo (e a) * dd a Wo f + ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo * dd a Wo f) ∧ 2 * (rsT (h.p i) Wo - rsT (h'.p i') Wo) + 2 * dlg Y.H Y.q.left Q.P.L (h.d i) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo * dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo = 2 * constFn Y.H.hom Wo π ∧ 2 * (rsT (h.p' i) Wo - rsT (h'.p' i') Wo) + 2 * ∑ a, constFn Y.H.hom Wo (h.u a) * dlg Y.H Y.q.left Q.P.L (dd a) (h.j i) (h'.j i') Wo - ∑ a, ∑ b, constFn Y.H.hom Wo (h.Θ a b) * dd a Wo (dlg Y.H Y.q.left Q.P.L (dd b) (h.j i) (h'.j i') Wo) = 2 * constFn Y.H.hom Wo π' := by
  first | exact @GlobalTheory.HeatUniqGlob.main | exact GlobalTheory.HeatUniqGlob.main | (intros; apply GlobalTheory.HeatUniqGlob.main <;> assumption)
