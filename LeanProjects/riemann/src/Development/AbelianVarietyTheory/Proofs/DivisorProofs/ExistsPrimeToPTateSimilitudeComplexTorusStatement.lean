import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  first | exact @GlobalTheory.UPel.HT.exists_tateIsoO_of_period | exact GlobalTheory.UPel.HT.exists_tateIsoO_of_period | (intros; apply GlobalTheory.UPel.HT.exists_tateIsoO_of_period <;> assumption)
