import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem normRepElig_of (hN : PairVal.NormRepExists D u u' F0 what₂) : NormRepElig u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨y, hy⟩ := hN γ w hγ.2 (PCount.eligRel_holds γ w hγ) hγ.1.1
  exact ⟨(w, y), hy⟩

theorem locClsE_of (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hO : ∀ Zd : TermLoc.LocDat D, PCount.InOrbZ Zd u u') : LocClsE M δ u u' F0 what₂ := by
  intro γ w hγ p
  refine ⟨fun a b => ?_, hO ⟨δ, M, hA⟩ w (zT γ) (PCount.atMat_zT hN hrows hγ (PCount.eligRel_holds γ w hγ)) p⟩
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of (normRepElig_of hN) hrows γ w hγ
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p
  simp only [yT, LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI a b) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.Coef
