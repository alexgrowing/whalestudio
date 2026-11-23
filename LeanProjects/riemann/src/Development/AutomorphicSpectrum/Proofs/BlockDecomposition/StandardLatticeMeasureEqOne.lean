import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat

theorem coordW_latV_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam v
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := (hlam v).1
  have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mv := GlobalTheory.CompanionTheory.SW.WBox.map_coordW (Fv F v) hK (lam v) 1 1
  have hset : (latV b v : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) =
      (GlobalTheory.CompanionTheory.SW.WBox.eW (Fv F v) hK 1 1) ⁻¹'
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mv.measure_preimage_equiv, Measure.pi_pi]
  simp [(hlam v).2]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat
