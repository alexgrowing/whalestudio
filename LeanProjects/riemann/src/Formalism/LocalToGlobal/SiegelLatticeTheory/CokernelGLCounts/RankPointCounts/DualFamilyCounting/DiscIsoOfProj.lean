import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def prO {X Y : Submodule K V} (hc : IsCompl X Y) : V →ₗ[𝓞 K] V :=
  (X.projection Y hc).restrictScalars (𝓞 K)

theorem prO_apply {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x = X.projection Y hc x := rfl

theorem prO_add {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x + prO hc.symm x = x :=
  Submodule.projection_add_projection_eq_self hc x

def toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y) (L Λ : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L)) :
    ↥Λ →ₗ[𝓞 K] DiscMod h X L 𝔭 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (prO hc ∘ₗ Λ.subtype) (fun x => hP x x.2)

theorem toDisc_surj (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (hS : ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, prO hc x = v) :
    Function.Surjective (toDisc h hc L Λ 𝔭 hP) := by
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, e⟩ := hS v hv
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩

theorem mem_ker_toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (x : ↥Λ) : x ∈ LinearMap.ker (toDisc h hc L Λ 𝔭 hP) ↔ prO hc (x : V) ∈ locF 𝔭 L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem prO_mem_iff {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by
  rw [← hX, Submodule.mem_inf]
  constructor
  · exact fun H => H.1
  · intro H
    exact ⟨H, Submodule.projection_apply_mem hc x⟩

theorem discIso_of_proj (h : V →ₗ⋆[K] V →ₗ[K] K) {U W : Submodule K V} (hc : IsCompl U W)
    {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M) (hW : Λ ⊓ W.restrictScalars (𝓞 K) = locF 𝔭 T)
    (hPU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M))
    (hSU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v)
    (hPW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h W T))
    (hSW : ∀ v ∈ locF 𝔭 (dualIn h W T), ∃ x ∈ Λ, prO hc.symm x = v) :
    Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h W T 𝔭) := by
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hPU) = LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hPW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hU, prO_mem_iff hc.symm hW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  exact ⟨((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hPU hSU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hPW hSW))⟩

end Formalism.L2.SG.Pf.G6
