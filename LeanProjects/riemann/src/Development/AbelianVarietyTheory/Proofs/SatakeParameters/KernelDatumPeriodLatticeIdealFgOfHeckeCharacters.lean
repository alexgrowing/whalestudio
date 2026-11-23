import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryDataStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem forall_val_of_heq_hom {E : Type} [Field E] {a b b' : ℕ} (hb : b = b') (P : ℂ → Prop)
    {f : HomE E a b → ℂ} {g : HomE E a b' → ℂ} (h : HEq f g) (hg : ∀ x, P (g x)) : ∀ x, P (f x) := by
  subst hb
  rw [eq_of_heq h]
  exact hg

theorem kernel_datum_of_hecke_character_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ
  obtain ⟨hFG, hsd⟩ := GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual D L hT Gi Gl K Y cX ex t
  refine ⟨hFG, fun u μ i hi c c' hpin => ⟨hsd u μ i c, hsd u μ (i + 1) c', ?_⟩⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, row, -, hyb, hE, hC1, -, hC2, -, hp⟩ := t.rd_chain u μ
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · intro x
    rw [hE i hlt c c' x]
    exact GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) i hlt _ _ _ _ x
  · subst heq
    intro x
    rw [hC1 c c' x]
    exact GlobalTheory.T.precedingStepDatum_integral_away_from_levels D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) _ _ _ _ x
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    obtain ⟨d, hd⟩ := (hp c').1 hpin
    refine forall_val_of_heq_hom (congrArg D.R.N (by omega : t.m2 + 1 + 1 = D.R.m))
      (IntOff (t.O u μ).S) (hC2 c c' d hd) fun x => ?_
    exact GlobalTheory.T.lastStep_data_integralAwayFrom_levels D L hT Gi Gl K Y cX ex t u μ _ _ d x (hyb c)

end GlobalTheory
