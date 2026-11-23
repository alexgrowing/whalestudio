import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.CapComm

open Formalism.REAL

theorem commute_qdet_of {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A} {x : A}
    (h : ∀ a b, Commute x (X a b)) (u : ℂ) : Commute x (qdet X u) := by
  have hm : ∀ a b, X a b ∈ Subalgebra.centralizer ℂ ({x} : Set A) := fun a b =>
    (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact (h a b).eq
  have hq : qdet X u ∈ Subalgebra.centralizer ℂ ({x} : Set A) := by
    unfold qdet qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    unfold Tm
    refine Subalgebra.add_mem _ ?_ (hm _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 hq x rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A}
    (hX : GlRel X) (u v : ℂ) : Commute (qdet X u) (qdet X v) :=
  commute_qdet_of (fun a b => qDetCentral A k X hX u a b) v

theorem capR_capS_commute (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ)
    (u v : ℂ) :
    Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧
      Commute (capS r s τ u) (capS r s τ v) := by
  have hE := glRel_Eop (E := E) (a := r + s) τ
  refine ⟨?_, ?_, ?_⟩
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.castAdd_injective _ _)) _ _
  · exact (GlobalTheory.CapHC.qdet_comm hE _ _).symm
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.natAdd_injective _ _)) _ _

end GlobalTheory.CompanionTheory.CTFin.CapComm

end
