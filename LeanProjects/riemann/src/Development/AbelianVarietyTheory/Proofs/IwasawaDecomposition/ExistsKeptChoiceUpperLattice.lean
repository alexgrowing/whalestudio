import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := by kcopy n.tp, xi := kc% n.xi, psi := kc% n.psi, tie := by kcopy n.tie, Q := n.Q, chrPsi := by kcopy n.chrPsi }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, kc% h2, kc% h3⟩, g.sep⟩
end

theorem layer_up : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → NX hL (NEb hL) K B f T w Z Wt p0 t nch n xd → Nonempty (NX hL (NEb hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  intro hL K B f T w Z Wt S' N h nch xd
  refine ⟨nchUp S' N h nch, xdUp S' N h xd, kept_up S' N h nch, ?_, nchT_up S' N h, goodO_up S' N h, ?_⟩
  · rintro rfl
    exact ⟨HEq.rfl, HEq.rfl⟩
  · rintro p0 t n p0' t' ⟨tp', xi', psi', tie', Q', chr'⟩ hs hg ⟨c, e, ⟨bk⟩⟩
    have e1 : tp' = (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :)) := tupTied_ext (xi'.trans ((by with_unfolding_all exact (n.xi.symm :)))) (psi'.trans ((by with_unfolding_all exact (n.psi.symm :))))
    subst e1
    obtain ⟨a', hA⟩ := (mvOf w Z S' N h).exists_at c.a
    refine Exists.elim (exists_row hL K B f T w Z Wt S' N h nch xd p0 t p0' t' hs hg
      (GlobalTheory.T.rowReadings_sameRows_identify_definiteForms K B f T w Z Wt S' N h p0 t p0' t' hs) (GlobalTheory.T.rows_same_geometric_half K B f T w Z Wt S' N h nch p0 t p0' t' hs hg)
      (tp' := (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :))) c.a ((by with_unfolding_all exact (a' :))) ((by with_unfolding_all exact (hA :))) c.row e) fun r' hr => hr.elim fun e' => ?_
    have hq : a'.Pq = (by with_unfolding_all exact (c.a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (hA.2.1 :)))
    have hsel : Set.range a'.Pq = (by with_unfolding_all exact ((Set.range w.I.sel) :)) := (congrArg Set.range hq).trans ((by with_unfolding_all exact (c.sel :)))
    exact ⟨⟨⟨(by with_unfolding_all exact (a' :)), (by with_unfolding_all exact (r' :)), (by with_unfolding_all exact (hsel :))⟩, (by with_unfolding_all exact (e' :)), ⟨(by with_unfolding_all exact (((mvOf w Z S' N h).bkLaw bk) :))⟩⟩⟩

end GlobalTheory.LayerMove
end
