import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_trivial_everywhere : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → GalHodge D T → ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π → (∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (D.naut.locG π w)) → (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) → ∀ w, D.naut.mono0 (D.naut.locG π w) := by
  first | exact @GlobalTheory.GoodRowMono.mono0_all | exact GlobalTheory.GoodRowMono.mono0_all | (intros; apply GlobalTheory.GoodRowMono.mono0_all <;> assumption)
