import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberThroughModelPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem zhAbove_surjective {X₁ : GSet} {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} (h : ZHAbove X₁ Y πY) :
    Function.Surjective πY := by
  obtain ⟨-, -, -, -, -, hH, hP⟩ := h
  haveI := hP
  have hc : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
  have hg : genericPoint X₁.M.Z ∈ Set.range πY := by
    refine ⟨Y.pt (IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    have e := congrArg (fun f : Sp X₁.Ω₁ ⟶ X₁.M.Z => f (IsLocalRing.closedPoint X₁.Ω₁)) hH
    simp only [Scheme.Hom.comp_apply] at e
    exact e.trans (X₁.M.pt_apply _)
  intro z
  have : z ∈ closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) := by
    rw [genericPoint_spec X₁.M.Z |>.def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.2 hg) hc) this

theorem exists_gMem_injective : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem X₁
  obtain ⟨y, hy⟩ := zhAbove_surjective hY z₁
  obtain ⟨V, i1, i2, i3, -, ev, X, i4, t, δ, 𝔫, -, -, -, hinj⟩ := GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY y hy
  exact ⟨V, i1, i2, i3, ev, X, i4, t, δ, hinj, ⟨𝔫⟩⟩

end GlobalTheory.GSep
