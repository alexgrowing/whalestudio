import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := fun x hx => hL.2 ▸ Submodule.subset_span hx

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) where
  fg := hA.1.sup hB.1
  span_eq_top := by
    rw [eq_top_iff, ← hc.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hA.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)
    · rw [← hB.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right)

theorem prO_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V} (hz : z ∈ A ⊔ B) : prO hc z ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add, prO_apply, prO_apply, Submodule.projection_apply_of_mem_left hc (hA a ha),
    (Submodule.projection_apply_eq_zero_iff hc).2 (hB b hb), add_zero]
  exact ha

theorem prO_locF {X Y : Submodule K V} (hc : IsCompl X Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime)
    {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V}
    (hz : z ∈ locF 𝔭 (A ⊔ B)) : prO hc z ∈ locF 𝔭 A := by
  obtain ⟨t, ht, htz⟩ := (LocF.mem_locF_iff hp _ z).1 hz
  refine (LocF.mem_locF_iff hp _ _).2 ⟨t, ht, ?_⟩
  rw [← LinearMap.map_smul]
  exact prO_sup hc hA hB htz

theorem discMod_finite [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hc : IsCompl U (orthK h U)) {M T Λ₀ N₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T)
    (hN₀ : Submodule.IsLattice K N₀) (hΛ₀ : locF 𝔭 N₀ = Λ₀)
    (hW : Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T)
    (hiW : ∀ x ∈ Λ₀, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T))
    (hpr : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ₀, prO hc.symm x = v) :
    Finite (DiscMod h (orthK h U) T 𝔭) := by
  subst hΛ₀
  have hp := h𝔭.isPrime
  obtain ⟨r, hr⟩ := LIOrb.exists_pow_smul_le hN₀ (isLattice_sup hc.symm hT hM) h𝔭
  have hsurj := toDisc_surj h hc.symm T (locF 𝔭 N₀) 𝔭 hiW hpr
  have hker : ((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)) ≤
      LinearMap.ker (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) := by
    rw [Submodule.smul_le]
    intro a ha y _
    rw [mem_ker_toDisc]
    have h1 : a • (y : V) ∈ locF 𝔭 (T ⊔ M) := hr (Submodule.smul_mem_smul ha y.2)
    exact prO_locF hc.symm hp (mem_of_isLatIn hT) (mem_of_isLatIn hM) h1
  haveI := LIOrb.finite_quot hN₀ h𝔭 r
  refine Finite.of_surjective (((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)).liftQ
    (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) hker) ?_
  intro d
  obtain ⟨y, rfl⟩ := hsurj d
  exact ⟨Submodule.Quotient.mk y, Submodule.liftQ_apply _ _ _⟩

theorem exists_lattice_locF {Λ L₁ L₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hL₁ : Submodule.IsLattice K L₁) (hL₂ : L₂.FG) (hΛ : locF 𝔭 Λ = Λ) (h1 : L₁ ≤ Λ)
    (h2 : Λ ≤ locF 𝔭 L₂) : ∃ Λ', Submodule.IsLattice K Λ' ∧ locF 𝔭 Λ' = Λ := by
  refine ⟨(L₁ ⊔ L₂) ⊓ Λ, ⟨(hL₁.fg.sup hL₂).of_le inf_le_left, ?_⟩, ?_⟩
  · rw [eq_top_iff, ← hL₁.span_eq_top]
    exact Submodule.span_mono (fun x hx => ⟨Submodule.mem_sup_left hx, h1 hx⟩)
  · have e := LIOrb.IA.locF_inf 𝔭 h𝔭.isPrime (L₁ ⊔ L₂) Λ
    rw [hΛ] at e
    rw [e]
    exact le_antisymm inf_le_right (le_inf (h2.trans (LocF.locF_mono 𝔭 le_sup_right)) le_rfl)

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
