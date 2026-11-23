import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_indDetK

theorem eq_of_eqOn_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (F F' : IndSp (stdBlocks d hd) ρ)
    (h : ∀ κ ∈ KO k (Fin n), F.1.1 κ = F'.1.1 κ) : F = F' := by
  have hfun : F.1.1 = F'.1.1 := by
    funext x
    obtain ⟨p, w, hw, rfl⟩ :=
      GlobalTheory.SmGL.MultiIrr.exists_parab_mul (GlobalTheory.SmGL.stdBlocks d hd) x
    rw [GlobalTheory.SmGL.parInd_law, GlobalTheory.SmGL.parInd_law,
      h w hw]
  exact Subtype.ext (Subtype.ext hfun)

end P_indDetK

theorem step_indDetK : InducedDeterminantTwist := by
  intro k _ _ _ _ s n d hd W _ _ ρ F F' h
  exact P_indDetK.eq_of_eqOn_KO d hd ρ F F' h

end UpperTheory.TNZ
