import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingHostsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeEigenformCopyTransferUpper
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesRestageOfCarry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideEigenformCopyTransfer
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
theorem multiplicity_lower_bound_of_restricted_copy_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ
  obtain ⟨cHk, hc⟩ := _root_.GlobalTheory.T.hecke_eigenform_copy_transfer_upper_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ
  obtain ⟨YS, X, hpq, hhk, hfi, ⟨ser⟩, htau⟩ := _root_.GlobalTheory.T.mem_of_series_carry_alt hPr hSer hL hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ cHk hc
  obtain ⟨b0, hX, heF⟩ := _root_.GlobalTheory.T.side_eigenform_copy_transfer_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ cHk hc X hpq YS.eF ser.sup YS.act hhk
  exact ⟨{ toLI := l'', b := { toSettingsFormsState := b0, YS := YS, eF := heF.symm, fi := hfi, ser := hX ▸ ser, tau := hX ▸ htau } }⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_pos_of_restricted_eigenform_copy_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt | exact _root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt <;> assumption)
end
end
