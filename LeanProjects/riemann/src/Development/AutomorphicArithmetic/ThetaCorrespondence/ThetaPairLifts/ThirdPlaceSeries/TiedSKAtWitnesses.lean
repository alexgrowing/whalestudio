import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPinMin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsSTrue
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE
namespace GlobalTheory.Mem.Top.Bl.WitSK
end GlobalTheory.Mem.Top.Bl.WitSK
open Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC Matrix in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∀ (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) (t : Formalism.L2.Ker.KerEntTied q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S → KPin q t → ∃ T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex, T.toTiedDataS = S ∧ T.ker = t ∧ (∀ u i hi, T.crd u i hi = 1) ∧ _root_.Formalism.L2.Rows.RowPinMinAlt T ∧ _root_.Formalism.L2.JointsSAlt S ∧ Nonempty (PLift (Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W)) := by
  intro hL p K q S t hS hKp
  obtain ⟨he, hTw⟩ := hS.tw
  have hK := hKp.std
  have hC : TC.StdC q.w.I q.w.l q.Z S.cols := hS.cols ▸ q.x.col.std
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hD : TC.StdDt q.w.I q.w.l q.Z S.full.1.base.dt := by
    have key : ∀ (C : ColsTiedSym (q.w.D q.Z)) (F : ColsFullS C), C = q.x.col.C → HEq F q.x.col.full →
        TC.StdDt q.w.I q.w.l q.Z F.1.base.dt := by
      intro C F hC' hF
      subst hC'
      cases hF
      exact q.x.col.stdDt
    exact key _ _ hS.cols hS.full
  have hcf : S.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst hS.chr
  have hdiv : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) S.n.cf q.O.ex.nch S.n.tp q.O.X) :=
    ⟨WitSK.of_sigma_eq hS.chr (fun c tp => Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) c q.O.ex.nch tp q.O.X) q.x.div.chr⟩
  have hψ : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) S.theta.W.ψ (-1) :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) A.W.ψ (-1)) q.x.th.std
  have hweq : Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.WeilCompatibleEquivariance A.W) q.x.th.weq
  refine ⟨{ S with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl,
    fun _ _ _ => rfl, ⟨fun u => ?_, fun u μ hμ _ h1 => ?_, q.x.what₂.r.Y.bu⟩,
    _root_.GlobalTheory.Mem.JointsTrue.joints_of_standard_character q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex S hC hD hcf hS.dt hdiv hψ, ⟨⟨hweq⟩⟩⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [GlobalTheory.Mem.Col2.TC.KerSK.sharp_heq hK.X_eq (GlobalTheory.Mem.Col2.TC.KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact q.w.ok.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (q.w.D q.Z)) (Units.val (1 : GL (Fin ((q.w.D q.Z).R.N i)) (q.w.D q.Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [GlobalTheory.Mem.Col2.TC.KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact _root_.GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw_alt q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex _ he hC hTw u μ hμ h1
end
