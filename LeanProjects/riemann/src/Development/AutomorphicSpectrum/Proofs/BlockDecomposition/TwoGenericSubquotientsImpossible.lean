import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLeStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCoreMain

theorem le_of_not_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] (T A B : Submodule ℂ V)
    (hT : Module.rank ℂ (V ⧸ T) ≤ 1) (hA : ¬ A ≤ B ⊔ T) : B ≤ T := by
  intro b hb
  by_contra hbT
  obtain ⟨a, haA, haBT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨r, hr⟩ := hv₀ (Submodule.Quotient.mk b)
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hbT
    rw [zero_smul] at hr
    exact (Submodule.Quotient.mk_eq_zero T).mp hr.symm
  have hmk : Submodule.Quotient.mk (p := T) (a - (s * r⁻¹) • b) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← hr, ← hs, smul_smul,
      mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_self]
  have ht : a - (s * r⁻¹) • b ∈ T := (Submodule.Quotient.mk_eq_zero T).mp hmk
  apply haBT
  have : a = (s * r⁻¹) • b + (a - (s * r⁻¹) • b) := by abel
  rw [this]
  exact Submodule.add_mem_sup (B.smul_mem _ hb) ht

theorem nonempty_equiv_of_generic {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hsup : ∀ X Y : Subrepresentation ρ,
      (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T)
    (A B C D : Subrepresentation ρ) (hBA : B ≤ A) (hDC : D ≤ C)
    (hAB : (subQuot A B).IsIrreducible) (hCD : (subQuot C D).IsIrreducible)
    (hA : ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T) (hC : ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T) :
    Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  have hBT : B.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hA
  have hDT : D.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hC
  have hAT : ¬ A.toSubmodule ≤ T := fun h => hA (h.trans le_sup_right)
  have hCT : ¬ C.toSubmodule ≤ T := fun h => hC (h.trans le_sup_right)
  have hET : ¬ (A ⊓ C).toSubmodule ≤ T := GlobalTheory.T.inf_not_in_codim_one_submodule ρ T hT A C (hsup A C) hAT hCT
  have hEA : A ⊓ C ≤ A := inf_le_left
  have hEC : A ⊓ C ≤ C := inf_le_right
  have hEB : ¬ A ⊓ C ≤ B := fun h => hET (le_trans h hBT)
  have hED : ¬ A ⊓ C ≤ D := fun h => hET (le_trans h hDT)
  have hfillB := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ A B (A ⊓ C) hBA hAB hEA hEB
  have hfillD := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ C D (A ⊓ C) hDC hCD hEC hED
  obtain ⟨e₁⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ A B (A ⊓ C) hEA hfillB
  obtain ⟨e₂⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ C D (A ⊓ C) hEC hfillD
  have hiB : (subQuot (A ⊓ C) B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁.symm hAB
  have hiD : (subQuot (A ⊓ C) D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂.symm hCD
  have hnot : ¬ A ⊓ C ≤ (A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D := by
    intro h
    apply hET
    have h3 : ((A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D).toSubmodule ≤ T := by
      rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
        Subrepresentation.toSubmodule_inf]
      exact sup_le (inf_le_right.trans hBT) (inf_le_right.trans hDT)
    exact (fun v hv => h3 (h hv) : (A ⊓ C).toSubmodule ≤ T)
  obtain ⟨e₃⟩ := GlobalTheory.T.irreducible_subquotients_equiv_of_not_le ρ (A ⊓ C) B D hiB hiD hnot
  exact ⟨(e₁.symm.trans e₃).trans e₂⟩

end GlobalTheory.CompanionTheory.GenCoreMain
