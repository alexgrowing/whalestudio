import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryDivisorAvoidsAbelianLocus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_divisor_avoids_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (n : ℕ),
    (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) → ∀ z, Y.jQ z ∉ ((BY.idealSheaf ^ n).comap (genι Y)).support := by
  first | exact @GlobalTheory.TorRef.jQ_not_mem_support_comap_pow | exact GlobalTheory.TorRef.jQ_not_mem_support_comap_pow | (intros; apply GlobalTheory.TorRef.jQ_not_mem_support_comap_pow <;> assumption)
