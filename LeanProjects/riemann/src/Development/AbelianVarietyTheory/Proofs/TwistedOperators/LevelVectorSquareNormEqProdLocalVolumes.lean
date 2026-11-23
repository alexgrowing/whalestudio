import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCardStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlacesStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm

theorem levelVector_squareNorm_eq_prod_localVolumes_alt : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  intro hLIS D G _ _ Pl0 T A Ks _ _ _ R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL Hl cl hP μ 𝓧 hμ
  have hL' := hL
  obtain ⟨hcore, -, -, -, -, -, -, hlev, -⟩ := hL'
  obtain ⟨-, e, he, hth⟩ := hlev
  subst hP
  have h1 := GlobalTheory.T.normSq_productDatumTheta_conjugateHalf R F hPM i t σ s (LevelP.ofLocal Hl cl) cμ cη m ω BW f₀ f c io hL e he
    (fun y => omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y)
    (fun PP z => GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) z)
    (GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product R i t Hl cl m) f hth μ 𝓧 hμ
  rw [h1]
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hexp : (Vc D i).rank * (Wc D i).rank = D.R.r ^ 2 + D.R.r * D.R.t := by rw [hV, hW]; ring
  simp_rw [fun PP => GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card (k := kP PP) D.R.r D.R.t hV hW (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP), hexp]
  rw [Finset.prod_union (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t)]
  congr 1
  · rw [← Finset.prod_attach R.Pg]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [div_eq_mul_inv]
    congr 3
    simp [GlobalTheory.LevelVecNorm.locH, PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have hn : PP ∉ R.Pg := fun h => Finset.disjoint_left.1 (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t) h hPP
    rw [div_eq_mul_inv]
    congr 2
    simp only [GlobalTheory.LevelVecNorm.locH, dif_neg hn]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv

end GlobalTheory.LevelVecNorm
