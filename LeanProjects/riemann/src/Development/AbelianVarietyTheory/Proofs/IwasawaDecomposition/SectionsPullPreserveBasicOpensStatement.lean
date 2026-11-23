import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsPullPreserveBasicOpens
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_pull_preserve_basic_opens : ∀ (X X' : Scheme.{0}) (F : X' ⟶ X) (L : LB X) (L' : LB X') (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (V : X.Opens) (θ : ∀ j, Γ(X, V ⊓ L.U j)), θ ∈ secOn L V → ∀ (W : X'.Opens), W ≤ F ⁻¹ᵁ V →
    ∃ θ' : (∀ i, Γ(X', W ⊓ L'.U i)), θ' ∈ secOn L' W ∧ ∀ (g : X') (i : L'.ι) (j : L.ι), g ∈ W → g ∈ L'.U i → F g ∈ L.U j →
      (g ∈ X'.basicOpen (θ' i) ↔ F g ∈ X.basicOpen (θ j)) := by
  first | exact @GlobalTheory.SecPullIso.secOn_pull_of_iso | exact GlobalTheory.SecPullIso.secOn_pull_of_iso | (intros; apply GlobalTheory.SecPullIso.secOn_pull_of_iso <;> assumption)
