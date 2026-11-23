import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧ (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧ (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔ ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧ ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) → rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  first | exact @GlobalTheory.DownLift.ReadAdj.rdAdj_read | exact GlobalTheory.DownLift.ReadAdj.rdAdj_read | (intros; apply GlobalTheory.DownLift.ReadAdj.rdAdj_read <;> assumption)
