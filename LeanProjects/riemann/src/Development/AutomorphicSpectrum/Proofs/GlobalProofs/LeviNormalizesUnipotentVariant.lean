import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem mem_frameStab_initCols {C : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (h : ∀ i : Fin r, i ≤ k → (matHom _ σ J g).1 *ᵥ (adMat F C)ᵀ i = (adMat F C)ᵀ i) :
    g ∈ frameStab σ J (initCols C k) ⊤ := by
  simp only [GlobalTheory.StdPar.frameStab, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
  refine ⟨1, ?_⟩
  rw [Units.val_one, Matrix.mul_one]
  ext i j
  have hjk : Fin.castLE (Nat.succ_le_of_lt k.isLt) j ≤ k := by
    rw [Fin.le_iff_val_le_val, Fin.val_castLE]
    exact Nat.lt_succ_iff.mp j.isLt
  exact congrFun (h _ hjk) i

theorem uPart_le_levi_general (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r)) :
    uPart σ J X Y T ≤ levi σ J X Y T := by
  intro g hg
  have hfix : ∀ y ∈ GlobalTheory.StdPar.colSpan F X (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T) ⊔
      GlobalTheory.StdPar.colSpan F Y (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T),
      (↑(GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g) : Matrix (Fin n) (Fin n) _) *ᵥ y = y := hg
  simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Subgroup.mem_inf]
  intro k hk
  constructor
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))

end General

theorem uPart_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)),
    uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y T
  exact uPart_le_levi_general X Y T

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
