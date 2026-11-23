import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPelReductionLieMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pel_reduction_lie_multiplicity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (maximalIdeal T.V) t), ∃ Q : PAT H (Sp T.V), (∀ (F : Type) [Field F] [IsAlgClosed F] (f : T.V →+* F), Function.Injective f → ∀ (τ : 𝓞 E →+* F) (N : ℕ), LieMult t.act (spMap f) τ N → ∃ n, LieMult Q.t.act (spMap f) τ n ∧ n + Module.finrank (𝓞 E) P.D.toPre.X = N) ∧ ∀ (k : Type) [Field k] (r : T.V →+* k), IsLocalHom r → IsAbPart t.G (spMap r) Q.t.G (spMap r) := by
  first | exact @GlobalTheory.BdDim.exists_pat_abPart | exact GlobalTheory.BdDim.exists_pat_abPart | (intros; apply GlobalTheory.BdDim.exists_pat_abPart <;> assumption)
