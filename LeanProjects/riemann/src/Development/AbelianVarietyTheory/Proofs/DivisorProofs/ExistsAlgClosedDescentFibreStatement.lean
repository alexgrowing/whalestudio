import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedDescentFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_alg_closed_descent_fibre : GlobalTheory.Published.SiegelToroidalIntegral → ∀ (T : Formalism.L2.Pj.CDVR) (P : Out.PolAV (Sp T.V)) (σ : T.V →+* ℂ) (K : Type) [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (P₁ : Out.PolAV (Sp ℂ)) (φ : P₁.A.left ⟶ P.A.left) (φ₀ : P₁.A.left ⟶ P₀.A.left) (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] (r : T.V →+* k), Function.Injective σ → TrLe K n → IsPolFibre σ P P₁ φ → IsPolFibre ι P₀ P₁ φ₀ → ∃ (k₀ : Type) (_ : Field k₀) (_ : IsAlgClosed k₀) (ι₀ : k₀ →+* k) (B : Over (Sp k₀)) (_ : GrpObj B), TrLe k₀ n ∧ IsAbelianScheme B ∧ SameFibre P.A (spMap r) B (spMap ι₀) := by
  first | exact @GlobalTheory.BdDim.SiegSpec.exists_small_fibre | exact GlobalTheory.BdDim.SiegSpec.exists_small_fibre | (intros; apply GlobalTheory.BdDim.SiegSpec.exists_small_fibre <;> assumption)
