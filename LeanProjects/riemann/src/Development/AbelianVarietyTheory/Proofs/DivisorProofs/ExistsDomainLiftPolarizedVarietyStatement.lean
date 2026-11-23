import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_domain_lift_polarized_variety : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (T : Formalism.L2.Pj.CDVR) (P : Out.PolAV (Sp T.V)) (σ : T.V →+* ℂ) (k : Type) [Field k] [IsAlgClosed k] (r : T.V →+* k), 3 ≤ n → Odd n → IsUnit (n : T.V) → P.g = g → Function.Injective σ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (ψ : T.V →+* V) (σ' : V →+* ℂ) (r' : V →+* k) (y : Sp V ⟶ F.X) (P' : Out.PolAV (Sp V)) (φ : P'.A.left ⟶ P.A.left) (α : P'.A.left ⟶ F.univ.A.left) (α₂ : (G2 P'.A).left ⟶ (G2 F.univ.A).left), Function.Injective σ' ∧ σ'.comp ψ = σ ∧ r'.comp ψ = r ∧ IsPolFibre ψ P P' φ ∧ IsGrpPullback P'.A F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P'.A P'.L) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.SiegPt.exists_siegel_point | exact GlobalTheory.SiegPt.exists_siegel_point | (intros; apply GlobalTheory.SiegPt.exists_siegel_point <;> assumption)
