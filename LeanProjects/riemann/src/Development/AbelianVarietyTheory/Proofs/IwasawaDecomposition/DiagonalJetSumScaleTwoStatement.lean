import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagonalJetSumScaleTwo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_jet_sum_scale_two : ∀ {S : Type} [CommRing S] {ρ : Type} (m : ℕ),
    (GlobalTheory.ExpUniqCh0.diag m).comp (jetSum (Finset.univ : Finset (Fin 2))) = (jetScale (fun _ => (2 : S)) : Jet S ρ m →ₐ[S] Jet S ρ m) ∧
    ∀ i : Fin 2, (GlobalTheory.ExpUniqCh0.diag m).comp (jetIn i) = AlgHom.id S (Jet S ρ m) := by
  first | exact @GlobalTheory.ExpUniqCh0.diag_comp_jet | exact GlobalTheory.ExpUniqCh0.diag_comp_jet | (intros; apply GlobalTheory.ExpUniqCh0.diag_comp_jet <;> assumption)
