import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

def unitPermNonzero {E : Type} [Field E] (q : Eˣ) :
    ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) ≃ ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) where
  toFun X := ⟨fun a i => (q : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : (q : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  invFun X := ⟨fun a i => ((q⁻¹ : Eˣ) : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : ((q⁻¹ : Eˣ) : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  left_inv X := by
    apply Subtype.ext
    funext a i
    simp
  right_inv X := by
    apply Subtype.ext
    funext a i
    simp

theorem Th_ofE_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  intro F E _ _ _ _ φ A q y
  unfold Th
  rw [← Equiv.tsum_eq (unitPermNonzero q)
    (fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)))]
  refine tsum_congr fun X => ?_
  congr 1
  funext a i
  have hq : ((ofE q : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (AF F) (q : E) := rfl
  have hX : ((unitPermNonzero q X).1 a i) = (q : E) * X.1 a i := rfl
  rw [Units.val_mul, hq, hX, map_mul]
  ring

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
