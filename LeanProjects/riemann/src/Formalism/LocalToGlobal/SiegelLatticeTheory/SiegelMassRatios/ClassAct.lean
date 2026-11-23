import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.L2.SG.ClassAct

open Formalism.UG Module

section Abstract

variable {G : Type} [Group G]

def Normalises (D K : Subgroup G) : Prop := ∀ δ ∈ D, ∀ κ ∈ K, δ * κ * δ⁻¹ ∈ K

theorem Normalises.inv_conj {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by
  have := h δ⁻¹ (D.inv_mem hδ) κ hκ
  simpa using this

def rtCl (Γ K : Subgroup G) (δ : G) (hδ : ∀ κ ∈ K, δ⁻¹ * κ * δ ∈ K) : ClassSet Γ K → ClassSet Γ K :=
  _root_.Quotient.map' (fun x => x * δ) (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, rfl⟩ := DoubleCoset.rel_iff.mp hab
    refine DoubleCoset.rel_iff.mpr ⟨γ, hγ, δ⁻¹ * κ * δ, hδ κ hκ, ?_⟩
    group)

def DiaFree (Γ K D : Subgroup G) : Prop :=
  ∀ x : G, ∀ δ ∈ D, DoubleCoset.mk Γ K (x * δ) = DoubleCoset.mk Γ K x → δ ∈ K

theorem diaFree_of_isNeat {Γ K K₀ D : Subgroup G} (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) :
    DiaFree Γ K D := by
  intro x δ hδ h
  obtain ⟨γ, hγ, κ, hκ, hx⟩ := (DoubleCoset.eq Γ K (x * δ) x).mp h

  have hst : (⟨γ⁻¹, Γ.inv_mem hγ⟩ : Γ) ∈ stabAt Γ K₀ x := by
    show x⁻¹ * γ⁻¹ * x ∈ K₀
    have e : x⁻¹ * γ⁻¹ * x = δ * κ := by
      calc x⁻¹ * γ⁻¹ * x = x⁻¹ * γ⁻¹ * (γ * (x * δ) * κ) := by rw [← hx]
        _ = δ * κ := by group
    rw [e]
    exact K₀.mul_mem (hD hδ) (hK hκ)
  rw [hn x] at hst
  have hγ1 : γ = 1 := by
    have := congrArg Subtype.val (Set.mem_singleton_iff.mp hst)
    simpa using this
  subst hγ1
  have e2 : δ = κ⁻¹ := by
    have : x * 1 = x * (δ * κ) := by
      calc x * 1 = x := mul_one x
        _ = 1 * (x * δ) * κ := hx
        _ = x * (δ * κ) := by group
    have := (mul_left_cancel this).symm
    exact eq_inv_of_mul_eq_one_left this
  rw [e2]
  exact K.inv_mem hκ

def AMFChi (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) : Submodule k (G → W) where
  carrier := {f | ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ((χ κ : kˣ) : k) • ρ γ (f g)}
  zero_mem' := by intro γ g κ; simp
  add_mem' := by
    intro f f' hf hf' γ g κ
    simp only [Pi.add_apply, hf γ g κ, hf' γ g κ, map_add, smul_add]
  smul_mem' := by
    intro c f hf γ g κ
    simp only [Pi.smul_apply, hf γ g κ, map_smul]
    rw [smul_comm]

def rtF (k : Type) [CommRing k] (W : Type) [AddCommGroup W] [Module k W] (δ : G) : (G → W) →ₗ[k] (G → W) :=
  LinearMap.funLeft k W (fun g => g * δ)

def FixAt (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) (D : Subgroup G) : Submodule k (G → W) :=
  AMFChi k Γ K ρ χ ⊓ ⨅ δ : D, LinearMap.ker (rtF k W (δ : G) - LinearMap.id)

theorem mem_FixAt {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W] {Γ K : Subgroup G}
    {ρ : Representation k Γ W} {χ : K →* kˣ} {D : Subgroup G} {f : G → W} :
    f ∈ FixAt k Γ K ρ χ D ↔ f ∈ AMFChi k Γ K ρ χ ∧ ∀ δ ∈ D, ∀ g : G, f (g * δ) = f g := by
  unfold FixAt
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun δ hδ g => congrFun (h2 δ hδ) g⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun δ hδ => funext fun g => h2 δ hδ g⟩

end Abstract

def FixedDim : Prop :=
  ∀ (G : Type) [Group G] (Γ K K₀ D : Subgroup G) (k : Type) [Field k] (W : Type) [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : Representation k Γ W) (χ : K →* kˣ),
    K ≤ K₀ → D ≤ K₀ → IsNeat Γ K₀ → Normalises D K →
    (∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ) →
    (∀ κ : K, (κ : G) ∈ D → χ κ = 1) →
    Finite (ClassSet Γ K) →
    finrank k (FixAt k Γ K ρ χ D) * K.relIndex D = finrank k (AMFChi k Γ K ρ χ)

end Formalism.L2.SG.ClassAct
