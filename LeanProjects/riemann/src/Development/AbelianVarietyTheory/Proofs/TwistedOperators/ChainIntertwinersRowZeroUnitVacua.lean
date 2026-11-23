import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dif_pos h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dif_neg h1, dif_pos h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
