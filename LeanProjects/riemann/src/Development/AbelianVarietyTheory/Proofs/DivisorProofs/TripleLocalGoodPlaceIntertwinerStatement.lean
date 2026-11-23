import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGoodPlaceIntertwiner
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_good_place_intertwiner : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
  ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)) (ν₀ : (Fv F v)ˣ →* ℂˣ) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
    Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
    (∀ Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∃ Ψ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a'),
      Ψ - Ψ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a') (Fv F v)) (Ψ' : Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
        Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.FullRankCoinv.lact ν₀ g Ψ' - Ψ'}) ∧
    (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
    (∀ u₀ : GL (Fin (a + a')) (Fv F v), GlobalTheory.JacBlock₂.IsUnipStd u₀ → ∃ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) ∧
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, n)) φ φ₁ ∧ ι φ₁ = fun Y => ι φ (Y * u₀.1)) ∧
    (∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, m)) φ φ₁ →
        ι φ₁ = ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) • fun Y => ι φ (Y * (GlobalTheory.JacBlock₂.diagFirst (e x)).1)) ∧
    ∀ x : (w.adicCompletion E)ˣ, ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) * (((ν₀ (e x))⁻¹ : ℂˣ) : ℂ) *
        GlobalTheory.SplitFlip.apow (e x) ((((a + a' : ℕ) : ℂ) - 2 * (a' : ℂ)) / 2) = ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.JacBridge.bridge | exact GlobalTheory.JacBridge.bridge | (intros; apply GlobalTheory.JacBridge.bridge <;> assumption)
