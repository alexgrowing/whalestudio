import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.KerVal

theorem fm_succ_mem_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hBs hUnf hJets u μ i hi x c'
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam : ∀ j τ, Col2.lamT (B.hcW u) j τ = lamTG ((I.tw l l0 Z).fm u μ) j τ := by
    intro j τ
    unfold Col2.lamT lamTG
    show Col2.shW _ _ = Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) j) _
    obtain ⟨c, hc⟩ := B.R.t_odd
    have h1 : (B.R.t + 1) / 2 = c + 1 := by omega
    have h2 : j * (B.R.t + 1) / 2 = j * (c + 1) := by
      rw [show j * (B.R.t + 1) = 2 * (j * (c + 1)) by rw [hc]; ring]; omega
    simp only [Col2.shW, Formalism.L2.Forms.shW]
    congr 1
    funext r
    show _ + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)) = _ - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [h1, h2]
    push_cast
    ring
  have hP : ((x.1 c').1 : Formalism.L2.DIV.Pol B.LL (Tau B.R) (B.R.N (i + 1))) ∈ polV (I.rec7 l Z) u (i + 1) := by
    have h1 := VV_le_WtPol (K := B.LL) (Col2.lamT (B.hcW u) (i + 1)) (x.1 c').2
    have e : (fun τ r => (Col2.lamT (B.hcW u) (i + 1) τ).natW r) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
      funext τ r
      rw [hlam]
      refine (hnat τ r).trans ?_
      congr 1
      funext τ' r'
      exact hw τ' r'
    rw [e] at h1
    exact h1
  refine ⟨Submodule.Quotient.mk ⟨_, hP⟩, ?_⟩
  funext y
  show evP O u μ (i + 1) ⟨_, hP⟩ y = _
  show (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
    GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL (x.1 c').1) ((O u μ).frm (i + 1) y) = _
  simp only [(O u μ).frm_de (i + 1) hi y]
  rw [hStd.frm u μ (i + 1) y]
  show _ = Formalism.L2.Col.evFr (gramC (1 : Matrix (Fin _) (Fin _) _) (embAt B.embLL B.tauLL)) (shiftOf (Col2.lamT (B.hcW u) (i + 1))) B.embLL (x.1 c').1 y
  refine Eq.trans ?_ (Formalism.L2.Col.evFr_apply _ _ _ _ _).symm
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    exact ((congrArg DomWeight.detShift (hlam (i + 1) τ)).trans (hds τ)).symm
  · exact GlobalTheory.PdvKm.evFr_map _ _ _ _

end GlobalTheory.Mem.KerVal
