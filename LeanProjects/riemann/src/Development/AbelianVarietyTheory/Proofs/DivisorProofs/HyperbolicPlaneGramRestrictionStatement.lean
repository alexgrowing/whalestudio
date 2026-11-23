import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneGramRestriction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_gram_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (v : Pl F) (τ : E →ₐ[F] Fv F v)
    (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ (εW : F) (hermW : ∀ i j, σ (W.J j i) = algebraMap F E εW * W.J i j) (hJW : IsUnit (W.J.map τ).det)
      (ε₁ : F) (herm₁ : ∀ i j, σ (W₁.J j i) = algebraMap F E ε₁ * W₁.J i j) (hJ₁ : IsUnit (W₁.J.map τ).det)
      (e : (Σ i : Fin 3, Fin (GlobalTheory.IndLineGL.blk3 n₁ i)) ≃ Fin n),
      ∃ c : GL (Fin n) (Fv F v),
        (∀ u ∈ GlobalTheory.SmGL.unipRad (Fv F v) e,
          GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW (c * u * c⁻¹) ∈ unip σ W H) ∧
        (∀ h : GL (Fin n₁) (Fv F v), IsLevi (W₁ := W₁) H 1 (GlobalTheory.SplitUnitLift.liftU hcm τ W₁.J ε₁ herm₁ hJ₁ h)
          (GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW
            (c * GlobalTheory.SmGL.leviEmb (Fv F v) e (GlobalTheory.IndLineGL.midIncl (Fv F v) n₁ h) * c⁻¹))) ∧
        ∀ t₁ t₂ : (Fv F v)ˣ, IsLevi (W₁ := W₁) H (GlobalTheory.JacGeom.idl hcm τ (t₁, t₂⁻¹)) 1
          (GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW
            (c * GlobalTheory.SmGL.leviEmb (Fv F v) e (GlobalTheory.IndLineGL.torusPt (Fv F v) n₁ t₁ t₂) * c⁻¹)) := by
  first | exact @GlobalTheory.SplitLiftCoord.exists_lift_coords | exact GlobalTheory.SplitLiftCoord.exists_lift_coords | (intros; apply GlobalTheory.SplitLiftCoord.exists_lift_coords <;> assumption)
