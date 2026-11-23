import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.MatVTransvection
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemTer

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Cut

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ M :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem M x hx

theorem cut_span (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Submodule.span K ((M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = X := by
  apply le_antisymm
  · rw [Submodule.span_le]; intro x hx; exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem M x (by rw [hM]; exact Submodule.mem_top)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hmem : a • x ∈ (M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine Submodule.mem_inf.mpr ⟨hax, ?_⟩
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul K]
      exact X.smul_mem _ hx
    have : x = (algebraMap (𝓞 K) K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem rk_cut (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := by
  rw [Formalism.HN.rkK, cut_span M hM X]

theorem fg_cut (M : Submodule (𝓞 K) V) (hM : M.FG) (X : Submodule K V) : (M ⊓ X.restrictScalars (𝓞 K)).FG :=
  Submodule.FG.of_le hM inf_le_left

end Cut

section Block

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}

def Φt (Φ : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V := ∑ i, Φ i ∘ₗ LinearMap.proj i

theorem Φt_apply (Φ : Fin n → V →ₗ[K] V) (x : Fin n → V) : Φt Φ x = ∑ i, Φ i (x i) := by
  simp [Φt, LinearMap.sum_apply]

theorem Ψt_apply (Ψ : Fin n → V →ₗ[K] V) (y : V) (j : Fin n) : (LinearMap.pi Ψ) y j = Ψ j y := rfl

structure BlockHyp (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V) (Γ : Matrix (Fin n) (Fin n) K) : Prop where
  det : Γ.det ≠ 0
  h1 : ∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = Γ j i • x
  h2 : ∀ i, ∀ x ∈ X, Φ i x ∈ Y
  h3 : ∀ j, ∀ y ∈ Y, Ψ j y ∈ X
  h4 : ∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)

variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}

theorem BlockHyp.psiPhi (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    LinearMap.pi Ψ (Φt Φ x) = matV Γ x := by
  funext j
  rw [Ψt_apply, Φt_apply, map_sum, matV_apply]
  exact Finset.sum_congr rfl fun i _ => H.h1 i j (x i) (hx i (Set.mem_univ i))

theorem BlockHyp.phi_mem (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    Φt Φ x ∈ Y := by
  rw [Φt_apply]
  exact Y.sum_mem fun i _ => H.h2 i _ (hx i (Set.mem_univ i))

theorem BlockHyp.psi_mem (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) :
    LinearMap.pi Ψ y ∈ Submodule.pi Set.univ fun _ : Fin n => X :=
  fun j _ => H.h3 j y hy

theorem BlockHyp.phi_inj (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X)
    (h0 : Φt Φ x = 0) : x = 0 := by
  have := H.psiPhi x hx
  rw [h0, map_zero] at this
  rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]

theorem BlockHyp.psi_inj (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) (h0 : LinearMap.pi Ψ y = 0) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := H.h4 y hy
  have hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun i _ => hx i
  have := H.psiPhi x hx'
  rw [Φt_apply] at this
  rw [h0] at this
  have hx0 : x = 0 := by rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]
  simp [hx0]

theorem BlockHyp.map_phi (H : BlockHyp X Y Φ Ψ Γ) :
    (Submodule.pi Set.univ fun _ : Fin n => X).map (Φt Φ) = Y := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact H.phi_mem x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := H.h4 y hy
    exact ⟨x, fun i _ => hx i, by rw [Φt_apply]⟩

theorem BlockHyp.map_psi (H : BlockHyp X Y Φ Ψ Γ) :
    Y.map (LinearMap.pi Ψ) = Submodule.pi Set.univ fun _ : Fin n => X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact H.psi_mem y hy
  · intro x hx
    have hx' : matV Γ⁻¹ x ∈ Submodule.pi Set.univ fun _ : Fin n => X := by
      intro k _
      rw [matV_apply]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
    refine ⟨Φt Φ (matV Γ⁻¹ x), H.phi_mem _ hx', ?_⟩
    rw [H.psiPhi _ hx', matV_inv_cancel Γ H.det]

theorem BlockHyp.finrank [FiniteDimensional K V] (H : BlockHyp X Y Φ Ψ Γ) : Module.finrank K Y = n * Module.finrank K X := by
  let f : (Fin n → X) →ₗ[K] Y := LinearMap.codRestrict Y
    (Φt Φ ∘ₗ LinearMap.pi (fun i => X.subtype ∘ₗ LinearMap.proj i))
    (fun x => H.phi_mem _ (fun i _ => (x i).2))
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
      rw [← sub_eq_zero, ← map_sub] at h
      have := H.phi_inj _ (Submodule.sub_mem _ (fun i _ => (x i).2) (fun i _ => (y i).2)) h
      funext i
      apply Subtype.ext
      have := congrFun this i
      simpa [sub_eq_zero] using this
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := H.h4 y hy
      refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
      apply Subtype.ext
      simp [f, Φt_apply]
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  simp

end Block

end PI.Dv.TIW
