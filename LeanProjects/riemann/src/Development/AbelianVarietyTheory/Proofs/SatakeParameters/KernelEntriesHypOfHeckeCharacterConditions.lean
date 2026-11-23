import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharactersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem hypFree_of_top_int : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree := by
  intro D L hT Gi Gl K Y cX ex t hTop hInt u μ i hi c c' hnp
  have hsd := (GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t).2 u μ
  refine ⟨hsd i c, hsd (i + 1) c', ?_⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, pT, -, -, -, -, -, hpin, -⟩ := hTop u μ
  have hi' : i = t.m2 + 1 := by
    by_contra hne
    exact hnp (hpin (i + 1) (by omega) c')
  subst hi'
  exact hInt u μ c c' hnp

theorem kerEntTied_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ hTop
  have h0 : t.Hyp0 := by
    first
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2 hQ
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2
  exact hypotheses_of_base_hypotheses D L hT Gi Gl K Y cX ex t h0
    (hypFree_of_top_int D L hT Gi Gl K Y cX ex t hTop (GlobalTheory.T.lastStepKernelData_integral_awayFromLevels D L hT Gi Gl K Y cX ex t hTop))

end GlobalTheory
