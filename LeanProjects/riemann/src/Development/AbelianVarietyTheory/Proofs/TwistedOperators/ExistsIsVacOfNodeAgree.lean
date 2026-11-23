import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isVac_of_nodeAgree {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}
    {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) {N₁ N₂ : GlobalTheory.Grid.Node D} {X₁ X₂ : GlobalTheory.ChiGrid.Node}
    (h₁ : NodeAgree N₁ W X₁) (h₂ : NodeAgree N₂ W X₂) (f : WO (G'.V X₁) (G'.V X₂) → ℂ)
    (hf : IsVacO W.ψ W.θ (G'.V X₁) (G'.V X₂) (W.cart X₁) (W.cart X₂) (G'.Λ X₁ : Set _) (G'.Λ X₂ : Set _) f) :
    ∃ f' : WO N₁.V N₂.V → ℂ, GlobalTheory.Grid.IsVac W.ψ W.θ false N₁ N₂ f' := by
  obtain ⟨V₁, S₁, M₁, Λ₁, β₁⟩ := N₁
  obtain ⟨V₂, S₂, M₂, Λ₂, β₂⟩ := N₂
  obtain ⟨sp₁, lat₁, cart₁, -⟩ := h₁
  obtain ⟨sp₂, lat₂, cart₂, -⟩ := h₂
  dsimp only at sp₁ sp₂ lat₁ lat₂ cart₁ cart₂
  subst sp₁ sp₂
  cases eq_of_heq lat₁
  cases eq_of_heq lat₂
  refine ⟨f, ?_⟩
  have c₁ := eq_of_heq cart₁
  have c₂ := eq_of_heq cart₂
  unfold GlobalTheory.Grid.IsVac GlobalTheory.Grid.cartS
  simp only [GlobalTheory.Grid.sgnM, cond]
  rw [c₁, c₂]
  exact hf

theorem exists_isVac_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∃ f : WO (G.Xp j).V (G.nX j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hA _ j hj
  have hp : (GlobalTheory.ChiGrid.Pair.top A.μ0 j).InRange D.R.m := by
    simp only [GlobalTheory.ChiGrid.Pair.InRange, GlobalTheory.ChiGrid.Pair.big, GlobalTheory.ChiGrid.Node.InRange]
    omega
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev hp
  obtain ⟨f', hf'⟩ := exists_isVac_of_nodeAgree W (hA.top j hj.le) (hA.top (j + 1) hj) f hf
  rw [hW.ψ, hW.θ] at hf'
  exact ⟨f', hf'⟩

end GlobalTheory.GridJoin
