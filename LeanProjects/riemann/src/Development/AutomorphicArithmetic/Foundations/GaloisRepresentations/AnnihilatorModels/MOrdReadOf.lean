import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exA (hIn : CountIn) (hOut : CountOut) {n : ℕ} {P : Type} {I : Fin (n + 1) → Type}
    (v : ∀ j, I j → P) {k H : Type} [Field k] [Finite k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (e : ∀ j, I j ≃ Gr k H j)
    (hn : Module.finrank k H = n) (hC : Module.finrank k C = 1) :
    ∃ (A : Submodule k (H ⧸ C) → P) (D : Submodule k (H ⧸ C) → Submodule k H),
      (∀ E, ¬ C ≤ D E) ∧ (∀ E, (D E).map C.mkQ = E) ∧
      (∀ E, Module.finrank k (D E) = Module.finrank k E) ∧
      (∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1) ∧
      ∀ E (j' : Fin (n + 1)) (hj' : Module.finrank k (D E) = j'),
        A E = v j' ((e j').symm ⟨D E, hj'⟩) := by
  classical
  have hex : ∀ E : Submodule k (H ⧸ C), ∃ D : Submodule k H, ¬ C ≤ D ∧ D.map C.mkQ = E := by
    intro E
    have hcard := hOut k H C hC E
    have hpos : 0 < Nat.card {D : Submodule k H // ¬ C ≤ D ∧ D.map C.mkQ = E} := by
      rw [hcard]
      exact pow_pos Nat.card_pos _
    obtain ⟨⟨D, hD⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨D, hD⟩
  choose D hDC hDE using hex
  have hrk : ∀ E, Module.finrank k (D E) = Module.finrank k E := by
    intro E
    rw [(hIn k H C hC).2.2 (D E) (hDC E), hDE E]
  have hlt : ∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1 := by
    intro E
    have h1 : Module.finrank k E ≤ Module.finrank k (H ⧸ C) := Submodule.finrank_le E
    have h2 : Module.finrank k (H ⧸ C) ≤ Module.finrank k H := Submodule.finrank_quotient_le C
    omega
  refine ⟨fun E => v ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩
      ((e _).symm ⟨D E, rfl⟩), D, hDC, hDE, hrk, hlt, ?_⟩
  intro E j' hj'
  obtain rfl : j' = ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩ := Fin.ext hj'.symm
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.ordReadOf_of :
    CountIn → CountOut → OrdReadOf := by
  intro hIn hOut q n P F I v k H _ _ _ _ _ C e hq hn hC h1 h2
  obtain ⟨A, D, hDC, hDE, hrk, hlt, hA⟩ := exA hIn hOut v C e hn hC
  refine ⟨k, H, _, inferInstance, _, _, inferInstance, C, A, e, hq, hn, hC, fun j i => ⟨fun hle => ?_, fun hnle => ?_⟩⟩
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : (j : ℕ) = Module.finrank k E + 1 := by
      rw [← (e j i).2, (hIn k H C hC).2.1 _ hle]
    let j' : Fin (n + 1) := ⟨Module.finrank k E, hlt E⟩
    have hj' : Module.finrank k (D E) = j' := hrk E
    have hs : ((e j') ((e j').symm ⟨D E, hj'⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j') ⟨D E, hj'⟩)
    rw [hA E j' hj']
    apply h2 j j' i
    · exact hj
    · exact hle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : Module.finrank k (D E) = j := by
      rw [hrk E, ← (e j i).2, (hIn k H C hC).2.2 _ hnle]
    have hs : ((e j) ((e j).symm ⟨D E, hj⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j) ⟨D E, hj⟩)
    rw [hA E j hj]
    apply h1 j i
    · exact hnle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
