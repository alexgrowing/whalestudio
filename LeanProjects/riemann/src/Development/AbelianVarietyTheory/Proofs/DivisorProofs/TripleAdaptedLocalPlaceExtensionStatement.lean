import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedLocalPlaceExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_adapted_local_place_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (h : 2 ≤ a + a') (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
    ∃ (t : E →ₐ[F] Fv F v) (c' : GL (Fin (a + a')) (Fv F v)),
      (∀ n ∈ unipRad (Fv F v) (linePlace h), ∃ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) ∧
        (mat u).map (piW t) = ((c' * n * c'⁻¹ : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v))) ∧
      ∀ x : (w.adicCompletion E)ˣ, ∃ y : (Fv F v)ˣ,
        ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) =
          (chrW X.α t y : ℂ) * (absPow (Fv F v) ((a' : ℂ) / 2) y : ℂ) ∧
        ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) =
          (chrW X.β t y : ℂ) * (absPow (Fv F v) ((a : ℂ) / 2) y : ℂ) ∧
        ∀ m : UA σ G.W.J, IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) →
          (mat m).map (piW t) = ((c' * leviEmb (Fv F v) (linePlace h) (firstBlockScalar (Fv F v) (a + a') y) * c'⁻¹ :
            GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) := by
  first | exact @GlobalTheory.LineFrame.geom_split | exact GlobalTheory.LineFrame.geom_split | (intros; apply GlobalTheory.LineFrame.geom_split <;> assumption)
