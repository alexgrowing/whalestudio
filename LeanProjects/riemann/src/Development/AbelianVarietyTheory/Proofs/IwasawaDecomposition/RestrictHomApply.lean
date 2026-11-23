import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def IsSubWD (a : WDRep h V) (S : Submodule ℂ V) : Prop :=
  (∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) ∧ ∀ v ∈ S, a.N v ∈ S

def restrictHom (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    Representation ℂ (Weil h) S where
  toFun σ := (a.ρ σ).restrict (hS σ)
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp

@[simp] theorem restrictHom_apply (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    ((restrictHom a S hS σ v : S) : V) = a.ρ σ v := rfl

def restrict (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) : WDRep h S where
  ρ := restrictHom a S hS.1
  N := a.N.restrict hS.2
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS.1 σ))
    (a.semisimple σ)
  nilpotent := by
    obtain ⟨k, hk⟩ := a.nilpotent
    have hp : ∀ (j : ℕ) (v : S), (((a.N.restrict hS.2) ^ j) v : V) = (a.N ^ j) v := by
      intro j
      induction j with
      | zero => intro v; simp
      | succ j ih =>
        intro v
        rw [pow_succ', End.mul_apply, pow_succ', End.mul_apply, ← ih]
        rfl
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [hp, hk]
    rfl
  comm σ := by
    ext v
    simp [restrictHom, a.comm_apply]

@[simp] theorem restrict_ρ_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S)
    (σ : Weil h) (v : S) : (((restrict a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl

@[simp] theorem restrict_N_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) (v : S) :
    (((restrict a S hS).N v : S) : V) = a.N v := rfl

def restrictρ (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    WDRep h S where
  ρ := restrictHom a S hS
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS σ))
    (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

@[simp] theorem restrictρ_ρ_apply (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    (((restrictρ a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl

@[simp] theorem restrictρ_N (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) : (restrictρ a S hS).N = 0 := rfl

def wtSpace (a : WDRep h V) (k : ℤ) : Submodule ℂ V :=
  absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2))

def strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (m + 1), S.map (N ^ (j : ℕ))

def lowPart (U : ℤ → Submodule ℂ V) (N : End ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ k : ℤ, U k ⊓ LinearMap.ker (N ^ (((m : ℤ) - k + 1) / 2).toNat)

example (a : WDRep h V) : IsSubWD a ⊤ ∧ IsSubWD a ⊥ :=
  ⟨⟨fun _ _ _ => trivial, fun _ _ => trivial⟩, ⟨fun _ v hv => by simp_all, fun v hv => by simp_all⟩⟩

theorem le_strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : S ≤ strand N S m := by
  intro v hv
  exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) ⟨v, hv, by simp⟩

end GlobalTheory.WeilDeligne.PrimDecomp
