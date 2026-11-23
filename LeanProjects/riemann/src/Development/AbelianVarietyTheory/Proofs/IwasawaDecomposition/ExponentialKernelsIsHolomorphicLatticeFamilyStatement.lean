import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (m g : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)), IsOpen B → IsHolTo (B ×ˢ Set.univ) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) → (∀ b ∈ B, IsExpAt t (y b) (ex b)) → IsLatFam B (fun b => {w | ex b w = 1}) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | exact GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker <;> assumption)
