import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Formalism.RealPlaceAnalysis.StatementE
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CapelliIntertw

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) :
    f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  simp only [Function.comp_apply, map_add, apply_ite, AlgHom.commutes, map_zero]

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')

def intertw : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') where
  carrier := {z | ∀ v, T (z.1 v) = z.2 (T v)}
  mul_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
    rw [ha, hb]
  add_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
    rw [ha, hb]
  algebraMap_mem' := by
    intro c v
    simp [Module.algebraMap_end_apply]

end GlobalTheory.CapelliIntertw

theorem GlobalTheory.capelli_intertw : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  intro M M' _ _ _ _ T n X Y hXY u p v
  let S := GlobalTheory.CapelliIntertw.intertw T
  let Z : Fin n → Fin n → S := fun a b => ⟨(X a b, Y a b), fun w => hXY a b w⟩
  let q : S := Polynomial.aeval (Formalism.REAL.qdet Z u) p
  have h1 : ((q : Module.End ℂ M × Module.End ℂ M').1) = Polynomial.aeval (Formalism.REAL.qdet X u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.fst ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  have h2 : ((q : Module.End ℂ M × Module.End ℂ M').2) = Polynomial.aeval (Formalism.REAL.qdet Y u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.snd ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  rw [← h1, ← h2]
  exact q.2 v
