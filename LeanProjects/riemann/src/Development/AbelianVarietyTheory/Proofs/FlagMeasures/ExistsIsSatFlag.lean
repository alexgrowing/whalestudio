import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSat

theorem mem_of_isSat (I : AutInst) (x : I.GA) {N : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (hN : Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) N) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I x) (hy' : y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) : y ∈ N := by
  set A : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    lamX I x ⊓ (Submodule.span I.E (N : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) with hA
  have hle : N ≤ A := fun z hz => ⟨hN.1 hz, Submodule.subset_span hz⟩
  have hAL : A ≤ lamX I x := inf_le_left
  have e : N = A := by
    by_contra hne
    have h1 := GlobalTheory.PointFlag.rkK_lt _ _ (GlobalTheory.PointFlag.frm_unit I x) (GlobalTheory.PointFlag.fg_of_le I x hAL)
      (GlobalTheory.PointFlag.isSat_of_le _ _ hN hle hAL) hne
    have h2 : Submodule.span I.E (A : Set (Fin I.n → I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) :=
      Submodule.span_le.2 fun z hz => hz.2
    exact absurd h1 (not_lt.2 (Submodule.finrank_mono h2))
  rw [e]
  exact ⟨hy, hy'⟩

theorem exists_isSatFlag : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) (x : I.GA), x ∈ typeSet I j B → ∃ S, IsSatFlag I (lamX I (1, x.2)) j S ∧ sizesAt I x.2 S x.1 ∈ B := by
  rintro I a j B x ⟨τ, hτ, S, hS, hj⟩
  refine ⟨S, ⟨hS.1, hS.2.1.monotone, hj, fun i y => ?_, ?_⟩, ?_⟩
  · have h := GlobalTheory.PointFlag.flag_sat hS i
    exact ⟨fun hy => ⟨h.1 hy, Submodule.subset_span hy⟩, fun hy => mem_of_isSat I x h hy.1 hy.2⟩
  · rw [hS.2.2.1]
    exact (GlobalTheory.FlagIso.flag_isotropic I x).1
  · have e : sizesAt I x.2 S x.1 = τ := funext fun i => (hS.2.2.2.2.1 i).2.2.2
    rw [e]
    exact hτ

end GlobalTheory.FlagSat
