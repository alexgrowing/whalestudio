import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
