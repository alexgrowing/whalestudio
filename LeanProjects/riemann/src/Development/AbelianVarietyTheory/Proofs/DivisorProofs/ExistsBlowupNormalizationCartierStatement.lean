import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupNormalizationCartier
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_normalization_cartier : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsProjOver s → Flat s → ∀ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) →
    ∃ (X'' X' : Scheme.{0}) (b : X'' ⟶ X) (ν : X' ⟶ X''), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧
      IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver (ν ≫ b ≫ s) ∧ Flat (ν ≫ b ≫ s) ∧
      IsProper (ν ≫ b) ∧ IsIso ((ν ≫ b) ∣_ X.basicOpen (p : Γ(X, ⊤))) := by
  first | exact @GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen | exact GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen | (intros; apply GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen <;> assumption)
