import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.CuspOfParam

theorem goodRow_cuspidal : ∀ (D : D7) (Rw : RowSide D), Nonempty D.nd.Loc → (∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ := by
  intro D Rw hLoc hW hG j hj1 hj2 σ hσ hgood
  obtain ⟨i⟩ := hLoc
  obtain ⟨π, hcsd, hralg, hsplit, -, -, -⟩ := hG j hj1 hj2 σ hσ hgood
  have hr : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hiso : ∀ w, Formalism.MainNotions.N.isoLoc D.nd D.naut [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] w = D.naut.locG π w := by
    intro w
    simp [Formalism.MainNotions.N.isoLoc, Formalism.MainNotions.N.spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have hpar : Formalism.MainNotions.N.HasParamW D.nd D.naut i σ [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hr, le_refl 1⟩
    · simp [Formalism.MainNotions.N.rankIso]
    · intro w hw
      rw [hiso w, hsplit w hw, hW i σ w]
  have h := D.bc_tie i σ _ hpar
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hcsd)
    (by
      intro p hp τ
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨hnd, hz⟩ := (D.naut.ralg_def π).1 hralg τ
      refine ⟨hnd, fun z hz' => ?_⟩
      obtain ⟨n, hn⟩ := hz z hz'
      exact ⟨n, by rw [hn]; simp⟩)
  show D.ntypes.bc σ = {(D.R.r, 1)}
  rw [h]
  simp

end GlobalTheory.HeightCounting.CuspOfParam
