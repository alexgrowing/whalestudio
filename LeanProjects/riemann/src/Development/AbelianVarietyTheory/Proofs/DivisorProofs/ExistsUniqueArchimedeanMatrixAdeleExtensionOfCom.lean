import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.ArchMatCoords

theorem existsUnique_at_map_piInf :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [Fintype β] (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ M : InfinitePlace F → Matrix α β ℂ, ∃! u : Matrix α β (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  intro F E _ _ _ _ _ σ α β _ _ τ hCM M
  have hex := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ hCM τ (fun w => M w i j)
  choose z hzA hz using hex
  refine ⟨Matrix.of fun i j => z i j, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact hzA i j a ha
  · intro w
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact hz i j w
  · rintro v ⟨hvA, hvM⟩
    ext i j
    simp only [Matrix.of_apply]
    have hd : v i j - z i j = 0 := by
      refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
      · intro a ha
        have h1 : (a • v) i j = 0 := by rw [hvA a ha]; rfl
        rw [Matrix.smul_apply] at h1
        rw [smul_sub, h1, hzA i j a ha, sub_zero]
      · intro w
        have h2 := congrFun (congrFun (hvM w) i) j
        rw [Matrix.map_apply] at h2
        rw [map_sub, h2, hz i j w, sub_self]
    exact sub_eq_zero.1 hd

end GlobalTheory.ArchMatCoords
