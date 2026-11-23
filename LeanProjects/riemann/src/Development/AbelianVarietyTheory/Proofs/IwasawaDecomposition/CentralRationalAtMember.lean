import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenRatAt

theorem transfer {K G Pl0 V : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G]
    (B B' : Formalism.L2.DIV.BlockDat K G Pl0) (hB : B = B') (ℓ : Formalism.L2.DIV.Lvl K G) (Q : V → V → Prop)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) → V) (e' : (Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) → V)
    (h : GlobalTheory.Mem.Top.Bl.SameOn e e') (a : MonoidAlgebra K G)
    (H : ∀ x, Q (e x) (e ((B.S.lvlOp B.r ℓ.P ℓ.ψ a).mulVec x))) (x' : Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) :
    Q (e' x') (e' ((B'.S.lvlOp B'.r ℓ.P ℓ.ψ a).mulVec x')) := by
  subst hB
  have he : e = e' := funext fun x => h.2 x x fun i i' hi => congrArg x (Fin.ext hi)
  subst he
  exact H x'

theorem famR_L_eq (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U U' : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr tr' : R3.TrI X.B px) (k : Fin X.toD7.R.m) (s : R3.TupU I U) (s' : R3.TupU I U')
    (h : s.1 = s'.1) : (R3.famR X I hX U Xg tr).A.fam.L k s = (R3.famR X I hX U' Xg tr').A.fam.L k s' := by
  obtain ⟨τ, hτ⟩ := s
  obtain ⟨τ', hτ'⟩ := s'
  cases h
  rfl

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}

set_option maxHeartbeats 1000000 in

theorem cenRat_of (t : RowsT K w Z Wt p0) (r : RXs t) : GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  intro s k z a ha x
  have h5 : (tAll w.I (t.r.Y.tup s)).1 = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have h3 := (r.all.cen (t.r.Y.tup s) z a ha).2.2 k
  exact transfer _ _ (famR_L_eq (w.st Z) w.I t.hX _ _ _ _ _ k _ _ h5) _
    (fun u v => (w.st Z).toD7.ntypes.cenMt (t.r.Y.tup s) ((k : ℕ) + 1) z ((w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) u) =
      (w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) v)
    (r.all.eMt k (t.r.Y.tup s)) (t.r.Y.eMt k s) (r.eMt_use k s) a h3 x

end Main

theorem cenRat_at : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r

end GlobalTheory.CenRatAt
