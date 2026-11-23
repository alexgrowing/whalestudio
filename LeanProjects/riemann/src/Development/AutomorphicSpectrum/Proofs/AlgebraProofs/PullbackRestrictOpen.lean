import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PullbackRestrict

theorem isPullback_restrict_opens :
    ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S},
      IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W →
        ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme),
          IsPullback u (v ∣_ D) (g ∣_ W) h := by
  intro P Q Y S c v g p H W D hD
  have hbot : (Y.homOfLE hD ≫ p ∣_ W) ≫ W.ι = D.ι ≫ p := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have s : IsPullback ((v ⁻¹ᵁ D).ι ≫ c) (v ∣_ D) g ((Y.homOfLE hD ≫ p ∣_ W) ≫ W.ι) := by
    rw [hbot]
    exact (isPullback_morphismRestrict v D).flip.paste_horiz H
  exact ⟨_, _, IsPullback.of_right' s (isPullback_morphismRestrict g W).flip⟩

end GlobalTheory.CompanionTheory.PullbackRestrict
