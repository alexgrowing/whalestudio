import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersParabolicInduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_characters_parabolic_induction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsSmoothChar (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ Z : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)),
        (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁)).map Z = ⊤ ∧
        (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), Z φ = 0 → φ ∈ augAt om B.v₁) ∧
        ∀ (g : GL (Fin (a + a')) (Fv F B.v₁)) (h : UA σ G.W.J), h ∈ UAt σ G.W (evFin F B.v₁) →
          (mat h).map (piW B.τ₁) = g.1 →
          ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁),
            Acts (evFin F B.v₁) (om (1, h)) φ φ₁ → Z φ₁ = pairInd (Fv F B.v₁) b hb χ g (Z φ) := by
  first | exact @GlobalTheory.ThetaIsoGood.exists_map_onto_pairInd | exact GlobalTheory.ThetaIsoGood.exists_map_onto_pairInd | (intros; apply GlobalTheory.ThetaIsoGood.exists_map_onto_pairInd <;> assumption)
