import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseRowCountEqFinrankTypePartBaseLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypicStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotropicRankIwasawaDecomposition

theorem finrank_isot_eq_isotL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (D.what₂.isot ((i : ℕ) + 1) π) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y i π
  have hle : Y.IL.prtW i π ≤ (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [Y.prtWE]
    exact Submodule.map_mono inf_le_left
  have e1 : D.what₂.isot ((i : ℕ) + 1) π =
      ((Y.IL.prtW i π).comap ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i).subtype).comap
        (Y.IL.jMj i).toLinearMap := by
    ext y
    exact Y.tied.lift.isot i π y
  rw [e1, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, Y.prtWE]
  exact LinearEquiv.finrank_map_eq PiTensorProduct.lift _

end GlobalTheory.Mem.R3.IsotropicRankIwasawaDecomposition

namespace GlobalTheory.Mem.R3

theorem isotRank_of_multEq : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.BasicNotions.Rows.IsotRank D.what₂ := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost hX hD hM j hj1 hj2 π
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [IsotropicRankIwasawaDecomposition.finrank_isot_eq_isotL D G Pl0 I0 T A3 Ks R F cG X0 Y i π,
    ← GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hX hD hM i π,
    GlobalTheory.T.baseRowCount_eq_finrank_typePart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost π]

end GlobalTheory.Mem.R3
