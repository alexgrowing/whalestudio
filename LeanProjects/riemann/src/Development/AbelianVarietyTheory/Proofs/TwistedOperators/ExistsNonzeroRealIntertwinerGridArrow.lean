import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCaseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiscreteSeriesModelNegSpaceTransferStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridJoinCubicSizeBound

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.ArrX

theorem vertex_par {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces)
    (i j : ℕ) (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  rcases i with _ | i
  · rw [GlobalTheory.Grid.parV_zero D hj]
    show (GlobalTheory.Grid.row0 R j).S = _
    rcases j with _ | j
    · rfl
    · by_cases hlt : j + 1 < D.R.m
      · rw [← GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R hlt]
        dsimp only [GlobalTheory.Grid.nodeY]
        rw [Nat.min_eq_left hlt.le]
      · rw [← GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R hlt]
        have hm : j + 1 = D.R.m := by omega
        rw [hm]
  · exact (hS.vert i j hi hj).par

theorem exists_intertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hHC hHost hSz F hCore hgap G' W hW G hS hC hSp hTh i j hi hj ω f hω hf
  have hθ : IsInfFam R.θ := hCore.models.inf
  obtain ⟨M₁, hcart, honb, hback⟩ := GlobalTheory.T.exists_discreteSeriesModel_negSpace_transfer (G.V (i + 1) j).M
  choose aS aT haS haT be de hdat hflip hlow using
    fun τ => GlobalTheory.GridJoin.ArrXPar.arrowX_par hSz hCore G hC i j hi hj τ
  have hSn := vertex_par G hS (i + 1) j hi hj
  have hSo := vertex_par G hS i j hi.le hj
  have hc : cart M₁ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) := funext fun τ => (hcart τ).trans rfl
  have ho : onb M₁ = onb (G.V (i + 1) j).M := funext honb
  have hfin := hf.isFinVec
  have hne : f ≠ 0 := by
    unfold GlobalTheory.Grid.IsVac IsVacO at hf
    obtain ⟨-, ⟨-, -, -, -, ⟨⟨p, hp⟩, hq⟩⟩⟩ := hf
    intro h0
    have h1 := hq p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hvac : GlobalTheory.Chain.IsVacVec R.ψ R.θ M₁ (G.V i j).M f :=
    ⟨hfin.1, hne, fun τ => by rw [hc]; exact hfin.2 τ⟩
  obtain ⟨It₁, hIt₁⟩ := GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase (GlobalTheory.Grid.sgn true (G.V (i + 1) j).V) (G.V i j).V
    (fun τ => ((G.V (i + 1) j).S τ).image fun x => (x.1, !x.2)) (G.V i j).S M₁ (G.V i j).M R.θ R.ψ
    (GlobalTheory.Grid.sLen D) aS aT hDS hHC hθ
    (fun τ => ⟨be τ, de τ, hdat τ, by rw [hSn]; exact hflip τ, by rw [hSo]; exact hlow τ⟩)
    _ _ (GlobalTheory.Grid.WRep.toSgn true ω) hω (fun τ => ⟨haS τ, haT τ⟩) f hvac
  obtain ⟨It, hIt⟩ := hback (G.V i j).M R.θ hθ ω _ It₁ hIt₁
  have hpt : GlobalTheory.Chain.ptOf R.ψ R.θ M₁ (G.V i j).M f =
      ⇑(GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) := by
    unfold GlobalTheory.Chain.ptOf GlobalTheory.Grid.fock
    rw [hc, ho]
  exact ⟨It, hpt ▸ hIt⟩

end GlobalTheory.GridJoin.ArrX
