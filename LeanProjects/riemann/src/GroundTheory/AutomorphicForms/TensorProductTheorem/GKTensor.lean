import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CoeToRepresentationApply
import GroundTheory.AutomorphicForms.TensorProductTheorem.KProjApplyEqSelfIff
import GroundTheory.AutomorphicForms.TensorProductTheorem.TwoFactorUnique
import GroundTheory.AutomorphicForms.TensorProductTheorem.Window

noncomputable section

universe u

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module RestrictedTensor CompactRep

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace GKTensor

section FixedEnd

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ L V} (hτ : IsSmooth τ)
  {H : Subgroup L} (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))

def fixedEnd : End ℂ V := (fixedVectors τ H).subtype ∘ₗ fixedProj τ hτ hHc hHo

theorem fixedEnd_apply_of_mem {v : V} (hv : v ∈ fixedVectors τ H) :
    fixedEnd hτ hHc hHo v = v :=
  fixedProj_apply_of_mem hτ hHc hHo hv

theorem fixedEnd_mem (v : V) : fixedEnd hτ hHc hHo v ∈ fixedVectors τ H :=
  (fixedProj τ hτ hHc hHo v).2

theorem fixedEnd_comm {T : End ℂ V} (hT : ∀ g, T * τ g = τ g * T) (v : V) :
    fixedEnd hτ hHc hHo (T v) = T (fixedEnd hτ hHc hHo v) := by
  let f : Representation.IntertwiningMap τ τ := ⟨T, hT⟩
  have := fixedProj_map hHc hHo hτ hτ f v
  exact congrArg Subtype.val this

theorem isWinProj_fixedEnd : IsWinProj τ (fixedEnd hτ hHc hHo) :=
  ⟨fun v => fixedEnd_apply_of_mem hτ hHc hHo (fixedEnd_mem hτ hHc hHo v),
    fun Y _ hy => fixedProj_mem hτ hHc hHo Y hy⟩

theorem range_fixedEnd : LinearMap.range (fixedEnd hτ hHc hHo) = fixedVectors τ H := by
  refine le_antisymm ?_ fun v hv => ⟨v, fixedEnd_apply_of_mem hτ hHc hHo hv⟩
  rintro _ ⟨v, rfl⟩
  exact fixedEnd_mem hτ hHc hHo v

end FixedEnd

variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} [CompactSpace K]

theorem _root_.GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.isKFinite {V : Type*} [AddCommGroup V]
    [Module ℂ V] (M : h.GKModule K V) : IsKFinite M.σ :=
  ⟨M.locallyFinite, M.hasContinuousCoeff⟩

variable (h K) in

structure GKLModule (L : Type*) [Group L] (V : Type*) [AddCommGroup V] [Module ℂ V] where

  gk : h.GKModule K V

  τ : Representation ℂ L V
  comm_ρ : ∀ X g, gk.ρ X * τ g = τ g * gk.ρ X
  comm_σ : ∀ k g, gk.σ k * τ g = τ g * gk.σ k

namespace GKLModule

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
  (Mx : GKLModule h K L V)

theorem rep_comm (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (g : L) :
    Mx.gk.rep a * Mx.τ g = Mx.τ g * Mx.gk.rep a :=
  Mx.gk.rep_comm (fun X => Mx.comm_ρ X g) (fun k => Mx.comm_σ k g) a

def fullRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K) × L) V :=
  prodRep Mx.gk.rep Mx.τ Mx.rep_comm

def IsIrreducible : Prop := Mx.fullRep.IsIrreducible

def IsAdmissible : Prop :=
  IsSmooth Mx.τ ∧ ∀ (H : Subgroup L), IsCompact (H : Set L) → IsOpen (H : Set L) →
    ∀ (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (kProj Mx.gk.isKFinite hc ∘ₗ (fixedVectors Mx.τ H).subtype))

set_option maxHeartbeats 2000000 in

theorem exists_equiv_outerTensor_gkl (hirr : Mx.IsIrreducible) (hadm : Mx.IsAdmissible) :
    ∃ (H : Subgroup L) (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))
      (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule) (N₁ N₂ : Submodule ℂ V),
      N₁ ≤ fixedVectors Mx.τ H ∧ N₂ ≤ fixedVectors Mx.τ H ∧
      N₂ ≤ LinearMap.range (kProj Mx.gk.isKFinite hc) ∧ N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ ∧
      (∀ b, ∀ n ∈ N₂, fixedEnd hadm.1 hHc hHo (Mx.τ b n) ∈ N₂) ∧
      (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁).IsIrreducible ∧
      (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂).IsIrreducible ∧
      ((∀ T : End ℂ ((mGenSubrep Mx.τ N₂).toSubmodule ⧸ mGenKernel Mx.τ (fixedEnd hadm.1 hHc hHo) N₂),
          (∀ b, T * mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b =
            mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b * T) → ∃ c : ℂ, T = c • 1) →
        Nonempty (Mx.fullRep.Equiv
          (outerTensor (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁)
            (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂)))) := by
  classical
  have hτ := hadm.1
  have hσK := Mx.gk.isKFinite
  have hVnt := nontrivial_of_irreducible hirr
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨H', hH'c, hH'sub⟩ := exists_openSubgroup_isCompact_subset
    ((hτ x₀).mem_nhds (stabilizerOf Mx.τ x₀).one_mem)
  set H : Subgroup L := H'.toSubgroup
  have hHc : IsCompact (H : Set L) := hH'c
  have hHo : IsOpen (H : Set L) := H'.isOpen
  have hx₀H : x₀ ∈ fixedVectors Mx.τ H := fun g hg => hH'sub hg

  have hVHK : ∀ k, ∀ y ∈ fixedVectors Mx.τ H, Mx.gk.σ k y ∈ fixedVectors Mx.τ H := by
    intro k y hy g hg
    rw [← Module.End.mul_apply, ← Mx.comm_σ, Module.End.mul_apply, hy g hg]
  have hVH0 : fixedVectors Mx.τ H ≠ ⊥ := fun hb => hx₀ (by
    have : x₀ ∈ (⊥ : Submodule ℂ V) := hb ▸ hx₀H
    simpa using this)
  obtain ⟨c, hc, y, hyH, hy0, hyc⟩ := exists_kProj_eq_self hσK hVHK hVH0
  set e₁ := kProj hσK hc
  set e₂ := fixedEnd hτ hHc hHo
  have he₁ : IsWinProj Mx.gk.rep e₁ :=
    isWinProj_kProj hσK hc fun Y k y hy => Mx.gk.apply_σ_mem Y k hy
  have he₂ : IsWinProj Mx.τ e₂ := isWinProj_fixedEnd hτ hHc hHo
  have he₁₂ : ∀ g, e₁ * Mx.τ g = Mx.τ g * e₁ := fun g => LinearMap.ext fun v =>
    kProj_comm hσK hc (fun k => (Mx.comm_σ k g).symm) v
  have he₂₁ : ∀ a, e₂ * Mx.gk.rep a = Mx.gk.rep a * e₂ := fun a => LinearMap.ext fun v =>
    fixedEnd_comm hτ hHc hHo (fun g => Mx.rep_comm a g) v
  have hee : e₁ * e₂ = e₂ * e₁ := LinearMap.ext fun v =>
    (kProj_comm hσK hc (T := e₂) (fun k => LinearMap.ext fun w =>
      fixedEnd_comm hτ hHc hHo (fun g => Mx.comm_σ k g) w) v)
  have hW : LinearMap.range (e₁ * e₂) ≤
      LinearMap.range (kProj hσK hc ∘ₗ (fixedVectors Mx.τ H).subtype) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨fixedProj Mx.τ hτ hHc hHo v, rfl⟩
  have hfin : FiniteDimensional ℂ (LinearMap.range (e₁ * e₂)) := by
    have := hadm.2 H hHc hHo c hc
    exact Submodule.finiteDimensional_of_le hW
  have hne : LinearMap.range (e₁ * e₂) ≠ ⊥ := by
    intro hb
    have : y ∈ LinearMap.range (e₁ * e₂) := ⟨y, by
      show e₁ (e₂ y) = y
      rw [fixedEnd_apply_of_mem hτ hHc hHo hyH, hyc]⟩
    rw [hb, Submodule.mem_bot] at this
    exact hy0 this
  obtain ⟨N₁, N₂, hN₁W, hN₂W, hN₁0, hN₂0, -, hN₂st, hπ₁, hπ₂, hequiv⟩ :=
    exists_equiv_outerTensor (hcomm := Mx.rep_comm) hirr he₁ he₂ he₁₂ he₂₁ hee hne
  have hWH : LinearMap.range (e₁ * e₂) ≤ fixedVectors Mx.τ H := by
    rintro _ ⟨v, rfl⟩
    show e₁ (e₂ v) ∈ fixedVectors Mx.τ H
    exact kProj_mem hσK hc hVHK (fixedEnd_mem hτ hHc hHo v)
  have hWc : LinearMap.range (e₁ * e₂) ≤ LinearMap.range (kProj hσK hc) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨e₂ v, rfl⟩
  exact ⟨H, hHc, hHo, c, hc, N₁, N₂, hN₁W.trans hWH, hN₂W.trans hWH, hN₂W.trans hWc, hN₁0, hN₂0,
    hN₂st, hπ₁, hπ₂, hequiv⟩

end GKLModule

end GKTensor

end GroundTheory.Automorphic
