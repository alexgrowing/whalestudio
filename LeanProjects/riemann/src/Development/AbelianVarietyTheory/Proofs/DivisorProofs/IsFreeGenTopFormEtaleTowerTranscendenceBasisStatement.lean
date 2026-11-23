import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasis
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_tower | exact GlobalTheory.FieldPair.isFreeGen_dForm_tower | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_tower <;> assumption)
