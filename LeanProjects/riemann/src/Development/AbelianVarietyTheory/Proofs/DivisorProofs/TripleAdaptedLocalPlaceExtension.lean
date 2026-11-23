import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineParabolicUnipotentBlocksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameLocalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameLocalTorusActionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

noncomputable section

theorem GlobalTheory.LineFrame.geom_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
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
  intro F E _ _ _ _ _ σ B a a' G X om om' hT h d₁ W₁ H' i₀ i₁ hA v hv w hw
  have hB := hT.base
  obtain ⟨τ⟩ := GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully F E σ hB.cm v hv.2
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hB.cm (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hB.cm τ) hw
  obtain ⟨hP, hJ⟩ := GlobalTheory.T.adapted_frame_det_ne_zero F E σ B _ _ _ _ i₀ i₁ G.W W₁ H' hB hT.geo.hW hA
  refine ⟨t, GlobalTheory.LineFrame.frameGL t H' hA.rank, fun n hn => ?_,
    fun x => ⟨GlobalTheory.LineFrame.locY t x, ?_, ?_, fun m hm _ => ?_⟩⟩
  · obtain ⟨Xm, Ym, hXY⟩ := GlobalTheory.T.line_parabolic_unipotent_blocks (Fv F v) _ _ hA.rank h n hn
    exact GlobalTheory.T.adapted_frame_local_determinant F E σ B _ _ _ _ i₀ i₁ G.W W₁ H' hB hT.geo.hW hA hP hJ v t n Xm Ym hXY
  · rw [GlobalTheory.LineFrame.twAbs_locIdele hB.cm]; push_cast; rfl
  · rw [GlobalTheory.LineFrame.twAbs_locIdele hB.cm]; push_cast; rfl
  · rw [GlobalTheory.LineFrame.locIdele_eq_idl hB.cm t x] at hm
    exact GlobalTheory.T.adapted_frame_local_torus_action F E σ B _ _ i₀ i₁ G.W W₁ H' hB.cm hA hP v t h _ m hm

end
