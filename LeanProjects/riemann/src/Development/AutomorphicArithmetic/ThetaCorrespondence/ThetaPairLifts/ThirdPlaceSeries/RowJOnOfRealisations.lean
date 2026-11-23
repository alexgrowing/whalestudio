import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowJOnOfRealisations
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0MapIotaEqTopOfRealStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.JOnRow
theorem row_jOn_of_realisations_alt : ∀ (Bd : BdT) (Q' : V4.Slot) (Lk : LkT Bd), Row Q' Lk (AtAll fun D O _ _ => ∃ (Rc : _root_.Formalism.L2.RecTAlt O.ex) (P : RowSideFamily O.ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s ∧ P.A3.fam3.TypesSep3 ∧ PrimRows3 Q.Rl Q.F) → R0.JInvariantConditionAtConstructedPoints Q' Lk := by
  intro Bd Q' Lk h
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ => ?_⟩⟩
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  obtain ⟨Rc, P, Dcf, Spf, Zscf, S, Ks, i1, i2, i3, Q, s, h1, h2, h3⟩ := hA Fm (w3_a hc) x hx' i
  exact _root_.GlobalTheory.T.V0_map_iota_eq_top_real_alt _ _ _ _ _ _ _ _ _ Rc P Dcf Spf Zscf S Ks i1 i2 i3 Q s h1 h2 h3
end GlobalTheory.JOnRow
end
end
