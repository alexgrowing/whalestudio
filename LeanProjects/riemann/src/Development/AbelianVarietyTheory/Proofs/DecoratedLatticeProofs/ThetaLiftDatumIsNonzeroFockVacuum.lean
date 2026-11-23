import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFockVac

theorem levVec_fockVac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hθf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m ω BW f₀ f c io h).1
  obtain ⟨hC, -, -, -, -, hW, -, hlv, -, -, -⟩ := h
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hlv
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf' : infPart D (cA D (cA D e)) = 0 := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.PlaceVec.idemSum_infPart he
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hr : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)
  have hf0 : f ≠ 0 := by
    have h00 : f₀ ≠ 0 := by
      rintro rfl
      obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
      have := h2 p hp
      simp [nrm2] at this
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
    rw [hall Tm hTm]
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    have hee : e * e = e := ho.idem
    obtain ⟨-, hFS, -⟩ := hC.lev.βV i
    obtain ⟨-, hFT, -⟩ := hC.lev.βW i
    have hSB := GlobalTheory.FinZeta.isSBHalf_levDatum D _ _ _ _ _ _ (R.datWp i P) (R.Q t) m _ e hS hT hFS hFT he
    refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D R.ψ _ _ _ _ (cA D e) f₀ _ Tm hψ hS hT ho.conj.idem
      (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h00 hSB ?_
    obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) hee
      (GlobalTheory.AdjDatumNe.rectOne _ _ _)
    obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
    have hint : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) := by
      rw [hx']; exact GlobalTheory.AdjDatumNe.isIntM_smul_rectOne hi _ _
    have hred : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t,
        redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _ := by
      intro PP hPP
      rw [hx', GlobalTheory.AdjDatumNe.redM_smul_rectOne hi PP (hres PP hPP)]
      rfl
    intro hz
    have := congrFun hz x
    rw [if_pos ⟨hx, hint⟩, GlobalTheory.PlaceDatum.omegaG_congr _ m _ (fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_left _ hP),
      GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ (y' := fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (GlobalTheory.Chain.StepVac.omegaG_rectOne hr _ m) (GlobalTheory.Chain.StepVac.omegaQ_rectOne le_rfl hr _ m _) this
  refine ⟨?_, hθf, fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ), fun τ => ?_⟩
  · have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std hθf hf0 hμ
    have e1 : l2 μ 𝓧 f f = GlobalTheory.RawLift.thetaIP μ 𝓧 f f := by
      show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = ∫ w in 𝓧, star (f w) * f w ∂μ
      congr 1
      funext w
      rw [mul_comm]
      rfl
    rw [e1]
    exact h1
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf hinf hinf' hth hv.theta hθf (hv.fock τ)

end GlobalTheory.LiftFockVac
