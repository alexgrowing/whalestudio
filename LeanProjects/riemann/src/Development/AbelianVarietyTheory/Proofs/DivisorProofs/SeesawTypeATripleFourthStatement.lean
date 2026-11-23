import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeATripleFourth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_triple_fourth : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (f₀ : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
    ∃ (m : ℕ) (Λ₁ Λ₂ : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F))
      (π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m)) (W' : Set (EuclideanSpace ℝ (Fin m))),
      Continuous π ∧ IsOpen W' ∧ π (1, 1) ∈ W' ∧ (∀ S, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) ∧
      (∀ p, π p = π (1, 1) → mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • incV F H.x) = incV F H.x) ∧
      ∀ (p : KAt K (evI F) × idelesAt E (evI F)) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
        ∃ ℓ : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] ℂ,
          (∀ g, ℓ g = ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' p.2.1))) (locOpInf (om (p.1.1, 1)) g)) y) ∧
          ∀ (s : EuclideanSpace ℝ (Fin m)) (g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
            ⇑g = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) (Λ₁ s, Λ₂ s) ⇑f₀ →
            ℓ g = Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ s (π p) : ℝ) : ℂ)) * ℓ f₀ := by
  first | exact @GlobalTheory.ArchEigen.exists_param_eigen | exact GlobalTheory.ArchEigen.exists_param_eigen | (intros; apply GlobalTheory.ArchEigen.exists_param_eigen <;> assumption)
