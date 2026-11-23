import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem swMeasC_succ (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J → PositivityTheory.PfSWUS.HMass.IsAnisoH σ J →
    ∀ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeasC σ J T hT := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro J hJ _ T hT hd
    exact hB F E σ hσ J hJ T hT hd
  | succ n ih =>
    intro J hJ ha T hT hd
    obtain ⟨t, x, ht, hx⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ (n + 1) T ⟨hT, hd⟩
    obtain ⟨g, T₁, hT₁, hb, -⟩ :=
      GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) T ⟨hT, hd⟩ t x ht hx
    obtain ⟨hdet, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hσ (n + 1) T₁ t
    have hT' := hblk hT₁.1
    have htE : algebraMap F E t ≠ 0 := by
      simpa using ht
    have hd' : (blockOne (algebraMap F E t) T₁).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero htE hT₁.2
    refine hS F E σ hσ (n + 2) J hJ (n + 2) T hT hd g _ hT' hb ?_
    by_cases hrep : ∃ y : Fin (n + 2) → E, hE σ J y y = algebraMap F E t
    · obtain ⟨y, hy⟩ := hrep
      obtain ⟨g', J₁, hJ₁, hb', -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) J hJ t y ht hy
      have ha' : PositivityTheory.PfSWUS.HMass.IsAnisoH σ (blockOne (algebraMap F E t) J₁) := by
        rw [hb']
        exact PositivityTheory.PfSWUS.HMass.isAnisoH_of_isometry σ J g' ha
      refine hI F E σ hσ (n + 2) J hJ g' _ hb' (n + 2) _ hT' hd' ?_
      exact hSt F E σ hσ (n + 1) J₁ hJ₁ (by omega) t ht ha' T₁ hT₁.1 hT₁.2 hT'
        (ih J₁ hJ₁ (PositivityTheory.PfSWUS.HMass.isAnisoH_of_block σ _ J₁ ha') T₁ hT₁.1 hT₁.2)
    · exact hN F E σ hσ (n + 1) J hJ (by omega) ha t ht T₁ hT₁.1 hT₁.2 hT' (fun y hy => hrep ⟨y, hy⟩)

theorem swMeasCAll_of (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) : SWMeasCAll := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ ha T hT hd
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  exact swMeasC_succ hB hI hS hSt hN F E σ hσ n J hJ ha T hT hd

end PositivityTheory.SiegelWeilFormula.Densx

end
