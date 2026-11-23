import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure Good {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} (hc : IsCompl U (orthK h U))
    (M T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) : Prop where
  iU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M)
  iW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T)
  oU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v
  oW : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ, prO hc.symm x = v
  cU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M
  cW : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem mk_eq_iff {X : Submodule K V} {L : Submodule (𝓞 K) V} (a b : ↥(locF 𝔭 (dualIn h X L))) :
    (Submodule.Quotient.mk a : DiscMod h X L 𝔭) = Submodule.Quotient.mk b ↔
      (a : V) - (b : V) ∈ locF 𝔭 L := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.mem_comap]

private theorem prO_mem' {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) : prO hc x ∈ X := by
  first
  | exact (Submodule.linearProjOfIsCompl X Y hc x).2
  | exact Submodule.projection_apply_mem hc x
  | exact Submodule.projection_apply_mem X Y hc x
  | simp [prO]
  | simp [prO, Submodule.projection]

private theorem prO_eq_zero_of_mem_compl {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ Y) :
    prO hc x = 0 := by
  have h1 : prO hc x ∈ X := prO_mem' hc x
  have h2 : prO hc x ∈ Y := by
    have e : prO hc x = x - prO hc.symm x := eq_sub_of_add_eq (prO_add hc x)
    rw [e]
    exact Y.sub_mem hx (prO_mem' hc.symm x)
  have h3 : prO hc x ∈ X ⊓ Y := Submodule.mem_inf.2 ⟨h1, h2⟩
  rw [hc.inf_eq_bot] at h3
  exact (Submodule.mem_bot K).1 h3

private theorem prO_eq_self_of_mem {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ X) :
    prO hc x = x := by
  have h0 : prO hc.symm x = 0 := prO_eq_zero_of_mem_compl hc.symm hx
  have e := prO_add hc x
  rw [h0, add_zero] at e
  exact e

theorem prO_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc' x ∈ U := prO_mem' hc' x

theorem prO_symm_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc'.symm x ∈ orthK h U := prO_mem' hc'.symm x

theorem orth_projection_of_mem_compl {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) : prO hc' x = 0 := by
  exact prO_eq_zero_of_mem_compl hc' hx

theorem orth_projection_symm_of_mem {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) :
    prO hc'.symm x = x := by
  exact prO_eq_self_of_mem hc'.symm hx

theorem prO_symm_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc'.symm x = 0 := by
  exact prO_eq_zero_of_mem_compl hc'.symm hx

theorem mem_of_proj (hG : Good hc M T 𝔭 Λ) {x x' : V} (hx' : x' ∈ Λ) (hU : prO hc x' = prO hc x)
    (hW : prO hc.symm x - prO hc.symm x' ∈ locF 𝔭 T) : x ∈ Λ := by
  have hle : locF 𝔭 T ≤ Λ := by
    rw [← hG.cW]
    exact inf_le_left
  have ht : prO hc.symm x - prO hc.symm x' ∈ Λ := hle hW
  have e1 := prO_add hc x
  have e2 := prO_add hc x'
  rw [hU] at e2
  have hx : x = x' + (prO hc.symm x - prO hc.symm x') := by
    calc x = prO hc x + prO hc.symm x := e1.symm
      _ = (prO hc x + prO hc.symm x') + (prO hc.symm x - prO hc.symm x') := by abel
      _ = x' + (prO hc.symm x - prO hc.symm x') := by rw [e2]
  rw [hx]
  exact Λ.add_mem hx' ht

def gam (hG : Good hc M T 𝔭 Λ) : DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭 :=
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hG.iU) =
      LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hG.iW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hG.cU, prO_mem_iff hc.symm hG.cW]
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
  ((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hG.iW hG.oW))

theorem gam_mk (hG : Good hc M T 𝔭 Λ) {x : V} (hx : x ∈ Λ) :
    gam hG (Submodule.Quotient.mk ⟨prO hc x, hG.iU x hx⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm x, hG.iW x hx⟩ := by
  have h1 : (Submodule.Quotient.mk ⟨prO hc x, hG.iU x hx⟩ : DiscMod h U M 𝔭) =
      toDisc h hc M Λ 𝔭 hG.iU ⟨x, hx⟩ := rfl
  have h2 : (Submodule.Quotient.mk ⟨prO hc.symm x, hG.iW x hx⟩ : DiscMod h (orthK h U) T 𝔭) =
      toDisc h hc.symm T Λ 𝔭 hG.iW ⟨x, hx⟩ := rfl
  rw [h1, h2, ← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ 𝔭 hG.iU)
    (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)]
  simp only [gam, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end Formalism.L2.SG.Pf.OrthogonalProjections
