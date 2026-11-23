import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfIsSplitOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepUnique
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteOfIsPullbackFpqc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.clopRep_finite_etale_of_constant_rank :
    ∀ {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) (n : ℕ), IsFinite G.hom → Etale G.hom → (∀ s, G.hom.finrank s = n) → UpperTheory.RepresentationRank.Rep G Y U → IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G Y U n hf he hn hR
  obtain ⟨S', t, h1, h2, h3, hs⟩ := GlobalTheory.FinEt.exists_isSplitOfRank_pullback G.hom hn
  obtain ⟨Y'', U'', hR'', hf'', he''⟩ := UpperTheory.exists_clopRep_of_isSplitOfRank ((Over.pullback t).obj G) n hs
  obtain ⟨U', hR'⟩ := UpperTheory.exists_clopRep_pullback t G Y U hR
  obtain ⟨e⟩ := UpperTheory.clopRep_unique _ _ _ _ _ hR' hR''
  have hcomp : pullback.snd Y.hom t = e.hom.left ≫ Y''.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hqf : IsFinite (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hqe : Etale (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hpb := IsPullback.of_hasPullback Y.hom t
  refine ⟨UpperTheory.isFinite_of_isPullback_fpqc _ _ _ _ hpb h3 inferInstance inferInstance hqf, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip ⟨⟨h3, inferInstance⟩, inferInstance⟩ hqe
