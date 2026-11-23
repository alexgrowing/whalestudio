import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL.SupportRing

namespace Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_hasSupport (hS : SubEmbedding) (x : IrrGL k) : ∃ s, HasSupport x.rep s := by
  obtain ⟨c, y, hd, hc, φ, hφ⟩ := hS k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  exact ⟨_, hasSupport_of_isSubquotient x.2.rep.irr hc (.of_injective φ hφ)⟩

theorem hasSupport_of_isSubquotient_prodIrr (hP : ProdSupport) {c N : ℕ} {y : Fin c → IrrGL k}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) :=
  hP k c N y hd t ht V π hi h

end Ysupp
