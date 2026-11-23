import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVeryAmpleOpensExist
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_very_ample_opens_exist : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower <;> assumption)
