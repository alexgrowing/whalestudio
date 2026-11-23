import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageOfPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Bare

set_option maxHeartbeats 2000000 in

theorem rows_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) : (p.ch true).n ≤ p.Dall := by
  rcases Nat.eq_zero_or_pos p.Dall with h0 | hpos
  · have h := p.D_eq
    rw [h0, Nat.cast_zero, mul_zero] at h
    have h' : (p.ch true).n = 0 := by exact_mod_cast h
    omega
  · rw [t.dall] at hpos ⊢
    have hF := Module.finite_of_finrank_pos hpos
    have h1 := LinearMap.finrank_range_of_inj (t.ch true).jE_inj
    have h2 := Module.finrank_eq_card_basis (p.ch true).bs.toBasis
    rw [Fintype.card_fin] at h2
    rw [← h2, ← h1, (t.ch true).jE_range]
    have hle := Mult.goodPart_le R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0
    have hf := Submodule.finiteDimensional_of_le hle
    refine le_trans ?_ (Submodule.finrank_mono hle)
    exact Submodule.finrank_map_le (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
      (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0)

set_option maxHeartbeats 2000000 in

theorem frames_unit {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) (v) : IsUnit (p.Xo v).det := by
  obtain ⟨_, -, h⟩ := t.rr
  exact (h v).2

end GlobalTheory.Mem.R3.Rw.Bare
