import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrict
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.klt_of_klt_restrict_alt : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  first | exact @GlobalTheory.FieldPair.klt_of_klt_restrict | exact GlobalTheory.FieldPair.klt_of_klt_restrict | (intros; apply GlobalTheory.FieldPair.klt_of_klt_restrict <;> assumption)
