import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B := by
  constructor
  · intro e
    rw [← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g A, ← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g B, e]
  · rintro rfl
    rfl

theorem gmap_inf (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap g A ⊓ Formalism.HermitianLatticesTheory.gmap g B := by
  ext x
  simp only [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]

theorem gmap_eq_self_of_fix (g : V ≃ₗ[K] V) {A : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, g x = x) :
    Formalism.HermitianLatticesTheory.gmap g A = A := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · intro hx
    have e := hA _ hx
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e]
    exact hx
  · intro hx
    have e := hA _ hx
    have : g.symm x = x := by
      conv_lhs => rw [← e]
      simp
    rw [this]
    exact hx

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {v : V} :
    v ∈ orthK h U ↔ ∀ u ∈ U, h u v = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem map_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {v : V} (hv : v ∈ orthK h U) : g v ∈ orthK h U := by
  rw [mem_orthK] at hv ⊢
  intro u hu
  have e1 : h (g u) (g v) = h u v := hg.1 u v
  rw [hg.2 u hu] at e1
  rw [e1, hv u hu]

theorem gmap_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g ((orthK h U).restrictScalars (𝓞 K)) = (orthK h U).restrictScalars (𝓞 K) := by
  have hgi : g⁻¹ ∈ isomFix h U := (isomFix h U).inv_mem hg
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem]
  constructor
  · intro hx
    have := map_mem_orthK hg hx
    simpa using this
  · intro hx
    exact map_mem_orthK hgi hx

theorem gmap_U {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
  gmap_eq_self_of_fix g fun x hx => hg.2 x hx

theorem dualF_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g (dualF h 𝔭 Λ) := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change (∀ y ∈ Formalism.HermitianLatticesTheory.gmap g Λ, h y x ∈ _) ↔ ∀ y ∈ Λ, h y (g.symm x) ∈ _
  constructor
  · intro H y hy
    have := H (g y) (by rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; simpa using hy)
    have e : h (g y) (g (g.symm x)) = h y (g.symm x) := hg y (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rwa [e] at this
  · intro H y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := H _ hy
    have e : h (g (g.symm y)) (g (g.symm x)) = h (g.symm y) (g.symm x) := hg _ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    rwa [e]

theorem le_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := by
  intro x hx
  rw [← hL.2]
  exact Submodule.subset_span hx

theorem fibP_gmap [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V) {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T := by
  have hMg : Formalism.HermitianLatticesTheory.gmap g M = M := gmap_eq_self_of_fix g fun x hx => hg.2 x (le_of_isLatIn hM x hx)
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap g
      invFun := Formalism.HermitianLatticesTheory.gmap g.symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => by
        have := Formalism.HermitianLatticesTheory.isomAct_gmap_symm g.symm Λ
        simpa using this }
  unfold fibP
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ ((∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Formalism.HermitianLatticesTheory.gmap g Λ) ∧
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g Λ ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T))
  have e1 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_U hg]
  have e2 : locF 𝔭 M = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) := by rw [LocalizedFibreSets.gmap_locF, hMg]
  have e3 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_orthK hg]
  have e4 : locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) := (LocalizedFibreSets.gmap_locF g 𝔭 T).symm
  rw [dualF_gmap hg.1, gmap_eq_iff, e1, e3, e4, gmap_eq_iff]
  conv_rhs => rw [e2, gmap_eq_iff]
  refine and_congr_left fun _ => ?_
  constructor
  · rintro ⟨Λ₀, h0, e0⟩
    exact ⟨Formalism.HermitianLatticesTheory.gmap g Λ₀, LocalizedFibreSets.isLattice_gmap g h0, by rw [← LocalizedFibreSets.gmap_locF, e0]⟩
  · rintro ⟨Λ₀, h0, e0⟩
    refine ⟨Formalism.HermitianLatticesTheory.gmap g.symm Λ₀, LocalizedFibreSets.isLattice_gmap g.symm h0, ?_⟩
    rw [← LocalizedFibreSets.gmap_locF, e0, Formalism.HermitianLatticesTheory.isomAct_gmap_symm]

end Formalism.L2.SG.Pf.G6
