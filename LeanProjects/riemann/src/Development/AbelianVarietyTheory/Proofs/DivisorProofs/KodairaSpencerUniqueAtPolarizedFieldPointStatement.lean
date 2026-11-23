import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (φ : Γ(X, U.1) →+* K) (P₀ : PolAV (Sp K)) (m : P₀.A.left ⟶ t.G.left), ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V → IsGrpPullback P₀.A t.G (spMap φ ≫ chart U) m → LBIso P₀.L (t.PP.L.pull m) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → IsKS t V U v D Θ' → φ.mapMatrix Θ = φ.mapMatrix Θ' := by
  first | exact @GlobalTheory.KSPtUniq.isKS_unique_at_point | exact GlobalTheory.KSPtUniq.isKS_unique_at_point | (intros; apply GlobalTheory.KSPtUniq.isKS_unique_at_point <;> assumption)
