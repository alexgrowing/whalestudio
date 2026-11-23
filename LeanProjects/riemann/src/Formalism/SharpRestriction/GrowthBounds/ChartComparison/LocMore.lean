import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocGoodLocJ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.CmpJMemSpan

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)

theorem locJ_iw_F (v : Fin (gatCh (gatJ Lv (i + 1)) em).P.nV) (a : D.host.F) :
    (locJ hi t B).iw v (algebraMap D.host.F D.host.E a) =
      ((locJ hi t B).eQ v).symm (algebraMap D.host.F (((locJ hi t B).pl v).1.adicCompletion D.host.F) a) :=
  congrArg ((locJ hi t B).eQ v).symm ((X.g u w hg).spl_F _ ((X.g u w hg).pl v).2 a)

theorem locJ_pos_emb {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D} (K : CmpTied D X T Gt c)
    (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E) :
    c.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (Fl.Pj (i + 1)).ι v (((Fl.Pj (i + 1)).σ v ^ s.val) ((locJ hi t B).iw v x)) :=
  (K.tie u w hg).pos_emb v s x

end Formalism.MainNotions.G.CmpJ

end
