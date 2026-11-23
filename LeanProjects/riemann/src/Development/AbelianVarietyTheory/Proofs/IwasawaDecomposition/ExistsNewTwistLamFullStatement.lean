import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFull
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_new_twist_lam_full : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}, K.Over B.toPre → Forced K B T → Start K B f T w → ∀ {P : Pre2 K w} (x : St P) (l : SettingsLevel hL x), ∃ N : TwNew (Dof x), (∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ ∀ (x' : St P) (l' : LI hL x'), x'.o = oTw x N → HEq l'.a.A.row (N.row l.a.A.row) → HEq l'.Pq l.Pq → HEq l'.rat.S (N.rat l.rat.S) → HEq l'.rat.In.Sb l.rat.In.Sb → HEq l'.rat.In.hL l.rat.In.hL → HEq l'.rat.In.eig l.rat.In.eig → HEq l'.rat.In.θ l.rat.In.θ → HEq x'.m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq x'.m.z.cG x.m.z.cG → HEq x'.m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → ∀ m : InMt x'.r.Y (cfOf x') w.I.xi (QOf P), (∀ i, GlobalTheory.MtRead.IdFrame x'.r.Y.hF (m.ad.PV i)) → Nonempty (SeriesState x'.m.z.geo l'.a l'.rat m.ad.PV l'.Pq) := by
  first | exact @GlobalTheory.HeightCounting.SerCopy.series_copy | exact GlobalTheory.HeightCounting.SerCopy.series_copy | (intros; apply GlobalTheory.HeightCounting.SerCopy.series_copy <;> assumption)
