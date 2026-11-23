import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_matrix : ∀ (l : ℕ) [Fact l.Prime] , ∃ c : ℝ, 0 < c ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (H : Subgroup ↥(GK K)) (Y : Matrix n n ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ∀ i j, ‖(Y.map (Formalism.Per.σC (g : GQ l)) - Y) i j‖ ≤ r) → ∃ Z : Matrix n n ℂ_[l], (∀ g ∈ H, Z.map (Formalism.Per.σC (g : GQ l)) = Z) ∧ ∀ i j, ‖(Y - Z) i j‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma_complete l
  refine ⟨c, hc, fun n _ _ K H Y r hr hY => ?_⟩
  have hent : ∀ i j, ∃ z : Om l, (∀ g ∈ H.map (GK K).subtype, g z = z) ∧
      ‖Y i j - (z : ℂ_[l])‖ ≤ c * r := by
    intro i j
    refine hax (H.map (GK K).subtype) (Y i j) r hr ?_
    rintro g' ⟨g, hg, rfl⟩
    have := hY g hg i j
    simpa [Matrix.sub_apply, Matrix.map_apply] using this
  choose z hz hzY using hent
  refine ⟨Matrix.of fun i j => (z i j : ℂ_[l]), ?_, ?_⟩
  · intro g hg
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact hz i j _ ⟨g, hg, rfl⟩
  · intro i j
    simpa [Matrix.sub_apply, Matrix.of_apply] using hzY i j

end GlobalTheory.AxLemma
