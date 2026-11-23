import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.Imports
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open Topology

namespace GlobalTheory.CuspRep

variable {G : Type} [Group G]

theorem isIrreducible_iff {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · have : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
        bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).1 ⟨⟨_, _, this⟩⟩
    · exact (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
        (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨h0, h⟩
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e : (⊥ : Submodule ℂ V) = ⊤)⟩⟩
    exact ⟨fun W => (h W.toSubmodule W.apply_mem_toSubmodule).imp
      (fun e => Subrepresentation.toSubmodule_injective e) (fun e => Subrepresentation.toSubmodule_injective e)⟩

@[simp] theorem twRep_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (g : G) (v : V) : twRep ρ χ g v = ((χ g : ℂˣ) : ℂ) • ρ g v := rfl

variable [TopologicalSpace G]

variable (G) in

structure SmIrr where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : GlobalTheory.PRep.IsSmooth ρ
  irred : ρ.IsIrreducible

attribute [instance] SmIrr.acg SmIrr.mod

variable (G) in

instance SmIrr.setoid : Setoid (SmIrr G) where
  r σ σ' := Nonempty (σ.ρ.Equiv σ'.ρ)
  iseqv := ⟨fun σ => ⟨.refl σ.ρ⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

variable (G) in

def Irr : Type 1 := Quotient (SmIrr.setoid G)

variable (G) in

def SmIrr.triv : SmIrr G where
  V := ℂ
  ρ := Representation.trivial ℂ G ℂ
  smooth v := by simp
  irred := (isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

instance : Inhabited (Irr G) := ⟨Quotient.mk _ (SmIrr.triv G)⟩

variable [IsTopologicalGroup G]

def SmIrr.twist (σ : SmIrr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : SmIrr G where
  V := σ.V
  ρ := twRep σ.ρ χ
  smooth v := isOpen_stab_of_mem_nhds _ v <| Filter.mem_of_superset
    (((σ.smooth v).inter hχ).mem_nhds ⟨by simp, by simp⟩) fun g hg => by
      have h1 : σ.ρ g v = v := hg.1
      have h2 : χ g = 1 := hg.2
      simp [h1, h2]
  irred := by
    obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ.irred
    refine (isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact (W.smul_mem_iff (Units.ne_zero (χ g))).1 (hW g v hv)

def Irr.twist (σ : Irr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.map (sa := SmIrr.setoid G) (sb := SmIrr.setoid G) (fun σ : SmIrr G => σ.twist χ hχ) (fun σ σ' ⟨e⟩ => ⟨.mk e.toLinearEquiv fun g => by
    ext v
    change e (((χ g : ℂˣ) : ℂ) • σ.ρ g v) = ((χ g : ℂˣ) : ℂ) • σ'.ρ g (e v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (e.isIntertwining' g) v)⟩) σ

def Irr.ofChar (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G := Quotient.mk _ ((SmIrr.triv G).twist χ hχ)

theorem Irr.ofChar_inj {χ χ' : G →* ℂˣ} {hχ : IsOpen {g | χ g = 1}} {hχ' : IsOpen {g | χ' g = 1}}
    (h : Irr.ofChar χ hχ = Irr.ofChar χ' hχ') : χ = χ' := by
  obtain ⟨e⟩ : Nonempty ((twRep (Representation.trivial ℂ G ℂ) χ).Equiv (twRep (Representation.trivial ℂ G ℂ) χ')) :=
    Quotient.exact h
  ext g
  have h1 : e (((χ g : ℂˣ) : ℂ) • (1 : ℂ)) = ((χ' g : ℂˣ) : ℂ) • e (1 : ℂ) :=
    LinearMap.congr_fun (e.isIntertwining' g) (1 : ℂ)
  rw [map_smul] at h1
  exact smul_left_injective ℂ ((map_ne_zero_iff e e.injective).2 (one_ne_zero (α := ℂ))) h1

end GlobalTheory.CuspRep
