import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_teichmuller_maps : ∀ (g : ℕ) (hg : g.Prime), (∃ τ : Fb g hg →* ℂ, ∀ x y, x ≠ 0 → y ≠ 0 → τ x = τ y → x = y) ∧ ∀ (l : ℕ) (hl : l.Prime), ∃ ι : Fb g hg →* Fb l hl, ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y :=
  fun g hg => ⟨@GaloisStage.exists_teichC g ⟨hg⟩, fun l hl => @GaloisStage.exists_iota g l ⟨hg⟩ ⟨hl⟩⟩

end GlobalTheory.MemN
