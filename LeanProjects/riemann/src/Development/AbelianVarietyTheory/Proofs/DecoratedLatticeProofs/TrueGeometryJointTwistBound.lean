import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowColumnEntryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam

theorem conv_single_one_of_forall {G : Type} [Monoid G] (l : List (G →₀ ℂ))
    (h : ∀ x ∈ l, x = Finsupp.single 1 1) : GlobalTheory.QPl.conv l = Finsupp.single 1 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x = Finsupp.single 1 1 := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    show List.foldr _ _ (x :: l) = _
    simp only [List.foldr_cons]
    change (x.sum fun g a => (GlobalTheory.QPl.conv l).sum fun h b => Finsupp.single (g * h) (a * b)) = _
    rw [hx, hl, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp

theorem chartZero_colOf : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ), (∀ t α, s t 0 α = 1) →
    (∀ t, ∃ w, PinChL (pk W) a.g (colOf a J kom dd S s cV cK cP t) a.c₀ (J t).A (J t).ι w) →
    GlobalTheory.MiTop.ChartZero (a.fam row (colOf a J kom dd S s cV cK cP)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr J hR row kom dd S s cV cK cP hs hpin t
  obtain ⟨w, hw⟩ := hpin t
  have hstd : ∀ β, (J t).A.kb 0 β = TC.kStd X u (B.R.N 0) :=
    (hR t).std 0 (by have := B.R.two_le_m; omega)
  have key := GlobalTheory.T.true_geometry_row_column_entry W hW u a ha hTr row (colOf a J kom dd S s cV cK cP) t (J t).Ch₀ (J t).A (J t).ι w a.c₀ hw hstd
  have hone : ∀ i, Fintype.card (((J t).E i).Ch 0) = 1 ∧ ∀ α, ((J t).E i).wt 0 α = 1 := fun i =>
    let h := GlobalTheory.T.bottom_spherical_card_weight_index _ _ _ _ _ _ _ ((J t).E i)
    ⟨h.1, h.2.1⟩
  have hU : ∀ i, Nonempty (Unique (((J t).E i).Ch 0)) := fun i =>
    (Fintype.card_eq_one_iff_nonempty_unique).1 (hone i).1
  let α₀ : (J t).Ch 0 := fun i => (hU i).some.default
  have hall : ∀ α : (J t).Ch 0, α = α₀ := fun α => funext fun i => (hU i).some.uniq (α i)
  refine ⟨α₀, hall, ?_, ?_⟩
  · show ((s t 0 α₀ • (J t).eps 0 α₀).mapDomain (· * a.g.b 0)) = _
    have hw1 : (J t).wt 0 α₀ = 1 := by
      unfold QJ.wt
      exact Finset.prod_eq_one fun i _ => (hone i).2 _
    have he : (J t).eps 0 α₀ = Finsupp.single 1 1 := by
      unfold QJ.eps
      rw [if_pos (Or.inr rfl), hw1, one_smul]
      apply conv_single_one_of_forall
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ((J t).E i).εL_zero _
    rw [hs, one_smul, he, Finsupp.mapDomain_single, one_mul]
  · exact key α₀

end GlobalTheory.Fam
