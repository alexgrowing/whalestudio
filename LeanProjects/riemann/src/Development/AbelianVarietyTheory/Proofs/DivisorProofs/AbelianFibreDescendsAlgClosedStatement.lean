import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianFibreDescendsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_fibre_descends_alg_closed : ∀ (k₀ k : Type) [Field k₀] [IsAlgClosed k₀] [Field k] [IsAlgClosed k] (ι : k₀ →+* k) (B : Over (Sp k₀)) [GrpObj B] (S : Scheme.{0}) (P : Out.PolAV S) (x : Sp k ⟶ S), IsAbelianScheme B → SameFibre P.A x B (spMap ι) → ∃ P₀ : Out.PolAV (Sp k₀), SameFibre P.A x P₀.A (spMap ι) := by
  first | exact @GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre | exact GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre | (intros; apply GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre <;> assumption)
