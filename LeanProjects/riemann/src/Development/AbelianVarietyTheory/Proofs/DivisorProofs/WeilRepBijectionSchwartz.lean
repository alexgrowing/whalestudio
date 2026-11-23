import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
open Matrix

namespace GlobalTheory.SchurHeisReindex

variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

noncomputable def eL (k : Type) [Field k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₗ[k] Matrix (Fin n) β k :=
  Matrix.reindexLinearEquiv k k (Equiv.refl (Fin n)) (Fintype.equivFin β).symm

theorem eL_apply (C : Matrix (Fin n) (Fin (Fintype.card β)) k) (i : Fin n) (b : β) :
    eL k n β C i b = C i (Fintype.equivFin β b) := by
  simp [eL, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem eL_symm_apply (D : Matrix (Fin n) β k) (i : Fin n) (j : Fin (Fintype.card β)) :
    (eL k n β).symm D i j = D i ((Fintype.equivFin β).symm j) := by
  simp [eL, reindexLinearEquiv_symm, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem continuous_eL : Continuous (eL k n β) := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [eL_apply]
  exact (continuous_apply _).comp (continuous_apply i)

theorem continuous_eL_symm : Continuous (eL k n β).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [eL_symm_apply]
  exact (continuous_apply _).comp (continuous_apply i)

noncomputable def eH (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₜ Matrix (Fin n) β k where
  toEquiv := (eL k n β).toEquiv
  continuous_toFun := continuous_eL
  continuous_invFun := continuous_eL_symm

theorem comp_mem_SB' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) : (f ∘ e) ∈ GlobalTheory.WeilM.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end GlobalTheory.SchurHeisReindex

open GlobalTheory.SchurHeisReindex in

theorem GlobalTheory.schur_heisenberg_linearModel_fintype : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n β _ _ Xt _ _ V ψ0 hψc hψ1 ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  set e := eL k n β with he
  let ι₁' : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ) := LinearMap.funLeft ℂ ℂ e ∘ₗ ι₁
  have hι₁' : ∀ x, ι₁' x = ι₁ x ∘ e := fun x => rfl
  let ι₂' : Xt → Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ := fun x => ι₂ x ∘ e
  have hsurj : Function.Surjective e := e.surjective
  have hbij' : Set.BijOn ι₁' (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin (Fintype.card β)) k) : Set _) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun f hf => ?_⟩
    · rw [hι₁']
      exact comp_mem_SB' (eH k n β) (hbij.1 hx)
    · apply hbij.2.1 hx hy
      rw [hι₁', hι₁'] at hxy
      funext Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact congrFun hxy Y
    · have hf' : f ∘ (eH k n β).symm ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) β k) := comp_mem_SB' (eH k n β).symm hf
      obtain ⟨x, hx, hxf⟩ := hbij.2.2 hf'
      refine ⟨x, hx, ?_⟩
      rw [hι₁', hxf]
      funext Y
      show f ((eH k n β).symm (e Y)) = f Y
      exact congrArg f ((eL k n β).symm_apply_apply Y)
  have hlin' : ∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂' (c • x + y) = c • ι₂' x + ι₂' y := by
    intro x hx y hy c
    funext Y
    simp [ι₂', hlin x hx y hy c]
  have hadd : ∀ Y C, e (Y + C) = e Y + e C := fun Y C => map_add e Y C
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat V ψ0 hψc hψ1 ι₁' ι₂' hbij' hlin'
    (fun C => Tr (e C)) (fun l => Mu (l ∘ₗ e.symm.toLinearMap))
    (fun C x hx => by
      obtain ⟨h1, h2, h3⟩ := hTr (e C) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2, hadd]
      · funext Y; simp [ι₂', h3, hadd])
    (fun l x hx => by
      obtain ⟨h1, h2, h3⟩ := hMu (l ∘ₗ e.symm.toLinearMap) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2]
      · funext Y; simp [ι₂', h3])
  refine ⟨c, fun x hx => ?_⟩
  funext Z
  obtain ⟨Y, rfl⟩ := hsurj Z
  have := congrFun (hc x hx) Y
  simpa [ι₂', hι₁'] using this
