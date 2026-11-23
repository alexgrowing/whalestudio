import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def whitFirstLin (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : X 0 →ₗ[ℂ] (PiTensorProduct ℂ X ⧸ whitKer ψ d (piTensor ρ)) :=
  (whitKer ψ d (piTensor ρ)).mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v 0

theorem whitFirstLin_apply (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) (x : X 0) :
    whitFirstLin ψ d ρ v x = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ (Function.update v 0 x)) := rfl

def whitFirstMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)) :=
  .mk (whitFirstLin ψ d ρ v) (fun g => by
    ext x
    have h : ∀ a, Function.update v 0 (ρ 0 g x) a = ρ a (firstEmb d g a) (Function.update v 0 x a) :=
      Fin.forall_fin_two.2 ⟨by simp [firstEmb], by simp [firstEmb]⟩
    simp only [LinearMap.comp_apply, whitFirstLin_apply, whit2_mk, piTensor_tprod]
    rw [funext h])

theorem whit_iSup_range_eq_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d X _ _ ρ
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have hmem : Submodule.Quotient.mk (PiTensorProduct.tprod ℂ v) ∈
        ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap := by
      refine Submodule.mem_iSup_of_mem (whitFirstMap ψ d ρ v) (LinearMap.mem_range.2 ⟨v 0, ?_⟩)
      show whitFirstLin ψ d ρ v (v 0) = _
      rw [whitFirstLin_apply, Function.update_eq_self]
    rw [Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ r hmem
  | add a b ha hb =>
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ ha hb

end GlobalTheory.CompanionTheory.BZNuPair
