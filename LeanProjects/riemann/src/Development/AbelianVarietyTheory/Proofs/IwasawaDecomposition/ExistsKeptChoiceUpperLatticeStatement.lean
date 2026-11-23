import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLattice
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kept_choice_upper_lattice : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → NX hL (NEb hL) K B f T w Z Wt p0 t nch n xd → Nonempty (NX hL (NEb hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  first | exact @GlobalTheory.LayerMove.layer_up | exact GlobalTheory.LayerMove.layer_up | (intros; apply GlobalTheory.LayerMove.layer_up <;> assumption)
