import Mathlib
import Formalism.PeriodIntegrals.WeylProd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem weylDim_of_weylProd (h : PI.WeylProd) {n : ℕ} (lam : DomWeight n) : WeylDim lam := by
  unfold WeylDim
  rw [Formalism.L2.G.Model.card_ssIdx]
  have hnn : ∀ t, ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.detShift := by
    intro t
    unfold DomWeight.natW
    apply Int.toNat_of_nonneg
    unfold DomWeight.detShift
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) t.isLt
    rw [dif_pos hn]
    have h1 : t ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      rw [Fin.le_def]
      have := t.isLt
      show t.val ≤ n - 1
      omega
    have := lam.anti h1
    omega
  have hanti : Antitone (fun t => ((lam.natW t : ℕ) : ℤ)) := by
    intro a b hab
    have := lam.anti hab
    simp only [hnn]
    omega
  have h1 := Formalism.L2.G.Model.weylQ n _ hanti
  have h2 : _ = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n := h n (fun t => ((lam.natW t : ℕ) : ℤ)) lam.w lam.detShift hnn
  rw [← h2, ← h1, Rat.cast_natCast]

theorem weylDim_holds {n : ℕ} (lam : DomWeight n) : WeylDim lam := weylDim_of_weylProd weyl_product_formula lam

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Inst

end Formalism.L2.Col
