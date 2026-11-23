import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.LamPos

theorem lambdaPrime_basis_row_type_pos_at_reference : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, ∀ j ∈ Finset.Icc 1 D.R.m, 0 < D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH hL hI σ j hj
  obtain ⟨cOf, -, h2, -⟩ := hL
  obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
  have hi : j - 1 < D.R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin D.R.m) : ℕ) + 1 = j := by simp only; omega
  have key := h2 ⟨j - 1, hi⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hI σ ⟨j - 1, hi⟩)
  rw [Y.tup0, hj'] at key
  rw [key]
  exact hH.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.R3.LamPos
end
