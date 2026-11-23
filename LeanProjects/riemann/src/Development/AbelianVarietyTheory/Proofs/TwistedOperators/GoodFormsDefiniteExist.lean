import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteIndexDimensionCounts
import Formalism.LocalToGlobal.IndefiniteReal.LinksExist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRows

theorem goodForms_definite_exist : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodVectorsDefinite → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥ := by
  intro hGV eps heps
  obtain ⟨x₀, hx₀⟩ := hGV.2 eps heps
  refine ⟨x₀, ?_⟩
  intro D L hP heps' hxL hSz G _ _ Pl0 T A Ks _ _ _ R F hGiv b

  have hTie : GlobalTheory.GLq.ESerTie D := by
    intro k
    obtain ⟨LD, hT, hE, _⟩ := hGiv.types k
    exact ⟨LD, hT, hE⟩

  obtain ⟨kap, lam, hScal⟩ := Formalism.IndefR.Links.scal_exists (F := F) R
  have hSet : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.HidaSetting (R.upd6 kap lam) F :=
    { lev := hGiv.core.lev
      grp := { hGiv.core.grp with }
      fam := { hGiv.core.fam with }
      models := { hGiv.core.models with }
      chain := Formalism.IndefR.Links.RealDat.chain_of_scalar_update hGiv.core.chain kap lam
      thP := Formalism.IndefR.Links.RealDat.theta_props_of_scalar_update hGiv.core.thP kap lam
      scal := hScal }

  obtain ⟨i, hi⟩ := GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.exists_last D
  have hShare := hx₀ D L hP heps' hxL hSz hTie G Pl0 T A Ks (R.upd6 kap lam) F hSet i hi b
  exact ⟨i, GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodShare.ne_bot (R.upd6 kap lam) F hShare⟩

end GlobalTheory.LiftRows

end
