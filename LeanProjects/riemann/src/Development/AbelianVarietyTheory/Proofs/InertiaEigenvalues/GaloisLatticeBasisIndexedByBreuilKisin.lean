import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.IdentRank

theorem basis_of_baseChange {O R N ι : Type} [CommRing O] [CommRing R] [Algebra O R] [Nontrivial R]
    [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N] [Fintype ι]
    (j : (ι → R) ≃ₗ[R] R ⊗[O] N) : Nonempty (Module.Basis ι O N) := by
  classical
  have : Nontrivial O := (algebraMap O R).domain_nontrivial
  let b := Module.Free.chooseBasis O N
  have h1 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis R b)
  have h2 := j.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, h1] at h2
  exact ⟨b.reindex (Fintype.equivOfCardEq h2.symm)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  have := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  obtain ⟨-, -, h3⟩ := GlobalTheory.WittTensorFixed.baseChange_flat (O := ↥(OL LL)) (frobW l) hs hk
    (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  have : Nontrivial (OW l ↥(OL LL)) := h3.nontrivial
  exact basis_of_baseChange I.j

end GlobalTheory.BKGal.IdentRank
