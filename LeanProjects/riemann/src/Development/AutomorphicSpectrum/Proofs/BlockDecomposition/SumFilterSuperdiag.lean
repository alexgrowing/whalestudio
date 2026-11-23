import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.WhitDict

theorem sum_filter_superdiag {k : Type} [Field k] {n : ℕ} (M : Matrix (Fin n) (Fin n) k) :
    (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, M p.1 p.2) =
      GroundTheory.Automorphic.Whittaker.superdiagSum M := by
  unfold GroundTheory.Automorphic.Whittaker.superdiagSum
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem whitChar_eq_psiN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)), ((whitChar ψ n u : ℂˣ) : ℂ) = GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) := by
  intro k _ _ _ _ ψ n u
  change ((Circle.toUnits (ψ (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) k).val p.1 p.2)) : ℂˣ) : ℂ) = _
  rw [sum_filter_superdiag]
  rfl

end GlobalTheory.CompanionTheory.WhitDict
