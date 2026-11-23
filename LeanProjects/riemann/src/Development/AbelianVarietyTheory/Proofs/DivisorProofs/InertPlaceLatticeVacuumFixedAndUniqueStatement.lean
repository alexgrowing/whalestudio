import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (AE F E)) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  first | exact @GlobalTheory.InertLatVac.vac_fixed_and_unique | exact GlobalTheory.InertLatVac.vac_fixed_and_unique | (intros; apply GlobalTheory.InertLatVac.vac_fixed_and_unique <;> assumption)
