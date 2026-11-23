import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.exists_rational_structure_lowest_form_space :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m),
      ∃ e : (Fin (lDim D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ (j.1 + 1),
        (∀ x, (X.R.HV j (Y.tupT μ)).e (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) (e x))) = (X.R.B.jL j (Y.tupT μ) (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ) x))) ∧
        OLatTie D.what₂.embLL (D.what₂.MtLat μ (j.1 + 1)) ((D.what₂.jMt μ (j.1 + 1)).comp e.toLinearMap) (lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ)) ∧
        Submodule.span ℂ (Set.range (D.what₂.jMt μ (j.1 + 1))) = ⊤ := by
  intro D X X0 Y μ hμ j
  have key : ∀ (t : _) (μ : D.what₂.Tup) (h : Y.tup t = μ) (hμ : Used0 D μ),
      ∃ e : (Fin (lDim D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ (j.1 + 1),
        (∀ x, HEq (Y.IL.jMt μ hμ j (D.what₂.jMt μ (j.1 + 1) (e x))).1
          (X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x)))) ∧
        OLatTie D.what₂.embLL (D.what₂.MtLat μ (j.1 + 1)) ((D.what₂.jMt μ (j.1 + 1)).comp e.toLinearMap) (lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t) ∧
        Submodule.span ℂ (Set.range (D.what₂.jMt μ (j.1 + 1))) = ⊤ := by
    intro t μ h hμ
    subst h
    refine ⟨Y.eMt j t, fun x => heq_of_eq (Y.mtRead j t hμ x), Y.latL j t, ?_⟩
    rw [eq_top_iff, ← (Y.formsL j t).span]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨e, h1, h2, h3⟩ := key (Y.tupT μ) μ (Y.tupTie μ hμ) hμ
  refine ⟨e, fun x => ?_, h2, h3⟩
  have h4 : formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) (e x)) =
      X.R.jV j (Y.tupT μ) (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT μ) x) :=
    Y.hinj j _ ((extV_formOf Y hμ j _).trans (eq_of_heq (h1 x)))
  rw [h4]
  exact X.char.models.jV _ _ _
