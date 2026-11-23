import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellDiag

def evalOne {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) :
    smoothPart (ind H σ) →ₗ[ℂ] W :=
  (LinearMap.proj (1 : G)).comp ((indSpace H σ).subtype.comp (smoothPart (ind H σ)).subtype)

theorem evalOne_injective {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) :
    Function.Injective (evalOne H σ) := by
  subst hH
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1 = 0 := hv
  have hmem : ∀ (h : (⊤ : Subgroup G)) (x : G),
      (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 (↑h * x) =
        σ h ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x) :=
    (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).2
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have key : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x =
      σ ⟨x, Subgroup.mem_top x⟩ ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1) := by
    have := hmem ⟨x, Subgroup.mem_top x⟩ 1
    rwa [mul_one] at this
  rw [key, h0, map_zero]
  first
  | rfl
  | simp

theorem dichotomy {V X T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup T] [Module ℂ T] [Module.Finite ℂ X] (hX : Module.finrank ℂ X ≤ 1)
    (hT : Module.finrank ℂ T = 1) (ι : V →ₗ[ℂ] X) (hι : Function.Injective ι)
    (φ ψ : V →ₗ[ℂ] T) : φ = 0 ∨ ∃ c : ℂ, ψ = c • φ := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  haveI : Module.Finite ℂ V := Module.Finite.of_injective ι hι
  have hV : Module.finrank ℂ V ≤ 1 := (LinearMap.finrank_le_finrank_of_injective hι).trans hX
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hφ (LinearMap.ext hne)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero φ)
  haveI : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hV1 : Module.finrank ℂ V = 1 := le_antisymm hV Module.finrank_pos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ v) hv).mp hT (ψ v)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hV1 w
  first
  | (rw [← ht, map_smul, map_smul, LinearMap.smul_apply, ← hc]; done)
  | (rw [← ht, ← hc]; simp [smul_comm])
  | (subst ht; simp [← hc, smul_smul, mul_comm])

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sizeMatrix_true_false {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0) :
    B.1 true false = 0 := by
  have hr := B.2.1 false
  have hc := B.2.2 false
  first
  | (rw [Fintype.sum_bool] at hr hc; omega)
  | (simp only [Fintype.sum_bool] at hr hc; omega)

theorem relParab_eq_top {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j) :
    relParab k (c := fun j i => Fin (B.1 i j)) g = ⊤ := by
  have h' := GlobalTheory.CompanionTheory.CellDiag.sizeMatrix_true_false B h
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.SmGL.relParab, Subgroup.mem_pi]
  intro j _
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro p q i i' hqp
  rw [Bool.lt_iff] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  exfalso
  cases j
  · have := i.isLt
    omega
  · have := i'.isLt
    omega

theorem diag_cell_at_most_one_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ B f g h φ ψ
  have hT : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    first
    | rw [Module.finrank_tensorProduct, Module.finrank_self]
    | simp [Module.finrank_tensorProduct]
    | simp
  refine GlobalTheory.CompanionTheory.CellDiag.dichotomy ?_ hT
    (GlobalTheory.CompanionTheory.CellDiag.evalOne _ _)
    (GlobalTheory.CompanionTheory.CellDiag.evalOne_injective _ (GlobalTheory.CompanionTheory.CellDiag.relParab_eq_top (k := k) B h g) _)
    φ.toLinearMap ψ.toLinearMap
  first
  | exact (Submodule.finrank_quotient_le _).trans hT.le
  | exact (Submodule.finrank_quotient_le _).trans (le_of_eq hT)
  | (refine (Submodule.finrank_quotient_le _).trans ?_; simp)

end GlobalTheory.CompanionTheory.CellDiag
