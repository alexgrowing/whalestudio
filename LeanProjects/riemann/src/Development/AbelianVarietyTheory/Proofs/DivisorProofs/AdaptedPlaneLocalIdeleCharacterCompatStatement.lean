import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLocalIdeleCharacterCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_local_idele_character_compat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ →
  ∀ (d d₁ r s : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
  ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (w : HeightOneSpectrum (𝓞 E)) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    (∀ x, piW t ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v)) →
    (∀ x, piW (t.comp σ) ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1) →
    (∀ x, At (evFin F v) (((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1)) →
    IsUnit (GlobalTheory.JacBridge.adaptQ t H').det ∧
    (∀ x (m : UA σ W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ W (evFin F v) ∧
      (mat m).map (piW t) = GlobalTheory.JacBridge.adaptQ t H' * (GlobalTheory.JacBlock₂.diagFirst (e x)).1 * (GlobalTheory.JacBridge.adaptQ t H')⁻¹) ∧
    ∀ u₀ : GL (Fin d) (Fv F v), GlobalTheory.JacBlock₂.IsUnipStd u₀ → ∀ n : UA σ W.J, n ∈ UAt σ W (evFin F v) →
      (mat n).map (piW t) = GlobalTheory.JacBridge.adaptQ t H' * u₀.1 * (GlobalTheory.JacBridge.adaptQ t H')⁻¹ → n ∈ unip σ W H' := by
  first | exact @GlobalTheory.JacBridge.Geom.adapted_basis_levi_unip | exact GlobalTheory.JacBridge.Geom.adapted_basis_levi_unip | (intros; apply GlobalTheory.JacBridge.Geom.adapted_basis_levi_unip <;> assumption)
