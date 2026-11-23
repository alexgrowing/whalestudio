import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegNcjm

theorem exists_perm_of_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) :=
  _root_.UpperTheory.Reformulated.B.Yhb6.main h

theorem exists_perm_one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL k)
    (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : IsSubquotient π (prodIrr x hx)),
    ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  intro k _ _ _ _ hA l N x hx hxc V _ _ π hs hi h
  obtain ⟨c, y, hy, hyc, φ, hφ⟩ := GlobalTheory.T.support_subscheme_embedding k N V π hs hi
  have h1 : HasSupport π (Finset.univ.val.map x) := hasSupport_of_isSubquotient hi hxc h
  have h2 : HasSupport π (Finset.univ.val.map y) := hasSupport_of_isSubquotient hi hyc (.of_injective φ hφ)
  have hm := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h2 h1
  have hcl : c = l := by simpa using congrArg Multiset.card hm
  subst hcl
  obtain ⟨e, he⟩ := exists_perm_of_map_eq hm
  obtain rfl : y = fun a => x (e a) := funext he
  refine ⟨e, hy, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hy π hs φ ?_⟩
  have : Nontrivial V := GlobalTheory.SmGL.nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩

end GlobalTheory.CompanionTheory.SegNcjm
