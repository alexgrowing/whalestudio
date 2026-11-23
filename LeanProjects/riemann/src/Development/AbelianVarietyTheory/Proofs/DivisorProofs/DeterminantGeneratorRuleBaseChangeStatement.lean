import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorRuleBaseChange
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_rule_base_change : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  first | exact @GlobalTheory.RealMult.Rule.eq_of_eq_extScalars | exact GlobalTheory.RealMult.Rule.eq_of_eq_extScalars | (intros; apply GlobalTheory.RealMult.Rule.eq_of_eq_extScalars <;> assumption)
