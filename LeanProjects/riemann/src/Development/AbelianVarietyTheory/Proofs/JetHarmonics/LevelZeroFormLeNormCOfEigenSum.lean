import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyLeOfEigenSum
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open scoped Matrix.Norms.Elementwise in

theorem ckOn_group_finset_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    (s : Finset ι) (Fi : ι → B.Mat k r → E) (h : ∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, Fi i g) := by
  intro g₀ hg₀
  choose U f hU hgU hf hff using fun i => h i g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun g => ∑ i ∈ s, f i g, isOpen_biInter_finset fun i _ => hU i,
    Set.mem_iInter₂.2 fun i _ => hgU i, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi => (hf i).mono fun g hg => Set.mem_iInter₂.1 hg i hi
  · intro g hg hG
    exact Finset.sum_congr rfl fun i hi => hff i g (Set.mem_iInter₂.1 hg i hi) hG

theorem levelZero_form_le_normC_of_eigen_sum : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (d : ℕ) (A : ℝ) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.AB P.k P.r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * P.r + P.k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV P.k P.r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV P.k P.r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re := by
  intro hXi Wp Wq _ _ _ _ _ _ P p lam d A nn F Y N hA hF hnn w hw _
  have hsm : B.CkOn ⊤ (B.GV P.k P.r) F := by
    obtain ⟨N₀, Fi, ν, -, hc, -, hsum⟩ := hF
    exact (ckOn_inCC_congr_on_group P.k P.r _ A (fun g => ∑ i, Fi i g) F
      (fun g hg => (hsum g hg).symm)).1 (ckOn_group_finset_sum Finset.univ Fi fun i => (hc i).1)
  have hs : M.sgn P p.l0 = 1 ∨ M.sgn P p.l0 = -1 := by
    unfold M.sgn
    exact neg_one_pow_eq_or ℂ _
  unfold KB.Pl.RR TBB.normC
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw.1)]
  exact GlobalTheory.levelZero_energy_le_of_eigen_sum hXi P.k P.r Wp Wq p.T.base lam d A _ nn F hs hA hF hnn w

end GlobalTheory
