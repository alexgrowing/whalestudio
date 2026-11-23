import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_pullback_tangent_vectors_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [CommRing K] (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) (A : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A t.G x0 θ → ∀ {m : ℕ} (u : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (u j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 u c w) → ∃ v : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j := by
  first | exact @GlobalTheory.LiePull.lieBasis_of_tanBasis | exact GlobalTheory.LiePull.lieBasis_of_tanBasis | (intros; apply GlobalTheory.LiePull.lieBasis_of_tanBasis <;> assumption)
