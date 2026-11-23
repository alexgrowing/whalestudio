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

variable {D : D7}

theorem exists_isVac_true_of_agree {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {N₁ N₀ : GlobalTheory.Grid.Node D} {V₁ V₀ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}
    {c₁ : D.what₂.Tau → Matrix (Fin V₁.rank) (Fin V₁.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin V₀.rank) (Fin V₀.rank) ℂ}
    (h₁ : N₁.V = V₁) (hΛ₁ : HEq N₁.Λ Λ₁) (hc₁ : HEq (Formalism.IndefR.Links.cart N₁.M) c₁)
    (h₀ : N₀.V = V₀) (hΛ₀ : HEq N₀.Λ Λ₀) (hc₀ : HEq (Formalism.IndefR.Links.cart N₀.M) c₀)
    {f : WO (negSp V₁) V₀ → ℂ} (hf : IsVacO ψ θ (negSp V₁) V₀ (fun τ => -c₁ τ) c₀ (Λ₁ : Set _) (Λ₀ : Set _) f) :
    ∃ f' : WO N₁.V N₀.V → ℂ, GlobalTheory.Grid.IsVac ψ θ true N₁ N₀ f' := by
  subst h₁ h₀
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₀
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₀
  exact ⟨f, hf⟩

end GlobalTheory.GridJoin

theorem GlobalTheory.GridJoin.exists_isVac_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ f : WO (G.P (i + 1)).V (G.P i).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hsp _ i hi
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .core i) (show (GlobalTheory.ChiGrid.Node.core (i + 1)).InRange D.R.m from (by show i + 1 ≤ D.R.m; omega))
  have a₁ := hsp.core (i + 1) (by omega)
  have a₀ := hsp.core i (by omega)
  unfold GlobalTheory.ChiGrid.GridData.Weil.IsVac at hf
  rw [hW.ψ, hW.θ] at hf
  exact GlobalTheory.GridJoin.exists_isVac_true_of_agree a₁.sp a₁.lat a₁.cart a₀.sp a₀.lat a₀.cart hf

end
