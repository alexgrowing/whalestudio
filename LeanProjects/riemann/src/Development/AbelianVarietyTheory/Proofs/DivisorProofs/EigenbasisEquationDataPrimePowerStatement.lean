import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisEquationDataPrimePower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_equation_data_prime_power : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} {E : Type} [Field E] [NumberField E]
    (A A' : Fin g → Adl C Y) (β : Fin g → (E →+* F)) (sh : (E →+* F) → ℝ)
    (ρ : 𝓞 E →+* Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (p n : ℕ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F), p.Prime → n ≠ 0 → IsUnit J.det → EigBasis ρ J sh p n P Q →
    (∀ k, EqData A A' β sh ρ J p k) → ∀ k, RelData A A' p n k := by
  first | exact @GlobalTheory.ConstLatRel.relData_of_eqData | exact GlobalTheory.ConstLatRel.relData_of_eqData | (intros; apply GlobalTheory.ConstLatRel.relData_of_eqData <;> assumption)
