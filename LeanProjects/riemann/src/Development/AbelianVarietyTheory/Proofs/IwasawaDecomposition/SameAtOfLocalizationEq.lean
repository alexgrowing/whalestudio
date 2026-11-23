import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

noncomputable section

namespace GlobalTheory.SameAtOfLoc

theorem exists_smul_mem_of_le_locP {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (𝓞 E) W] (Q : HeightOneSpectrum (𝓞 E)) {A B : Submodule (𝓞 E) W} (hA : A.FG)
    (h : A ≤ localization₂ Q.asIdeal B) : ∃ s ∉ Q.asIdeal, ∀ x ∈ A, s • x ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have key : ∃ s ∉ Q.asIdeal, ∀ a ∈ S, s • a ∈ B := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Formalism.L2.DIV.lc_one_notMem Q, by simp⟩
    | insert a S ha ih =>
      obtain ⟨s, hs, hS⟩ := ih (le_trans (Submodule.span_mono (by
        rw [Finset.coe_insert]; exact Set.subset_insert _ _)) h)
      obtain ⟨t, ht, hta⟩ := (Formalism.L2.DIV.lc_mem_locP Q B a).1
        (h (Submodule.subset_span (by simp)))
      refine ⟨t * s, Formalism.L2.DIV.lc_mul_notMem Q ht hs, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact B.smul_mem s hta
      · rw [mul_smul]; exact B.smul_mem t (hS b hb)
  obtain ⟨s, hs, hS⟩ := key
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem r hx

end GlobalTheory.SameAtOfLoc

namespace GlobalTheory

open GlobalTheory.SameAtOfLoc in

theorem sameAt_of_localized_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A →
    Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  intro E _ _ _ n Q A B hA hB h
  obtain ⟨a, ha, h1⟩ := exists_smul_mem_of_le_locP Q hB.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q B)
  obtain ⟨a', ha', h2⟩ := exists_smul_mem_of_le_locP Q hA.fg
    (h ▸ Formalism.L2.DIV.lc_le_locP Q A)
  exact ⟨a, ha, a', ha', h1, h2⟩

end GlobalTheory
