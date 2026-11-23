import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLevelDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CasimirEigenOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
  GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.DiscClosure

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

variable (E N) in

def autSub : Submodule ℂ (Sm E N) where
  carrier := {φ | IsAutForm φ}
  zero_mem' := isAutForm_const (Submodule.zero_mem _)
  add_mem' := fun {φ ψ} h h' => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add 1 h h'
  smul_mem' := fun c φ h => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add c h (isAutForm_const (Submodule.zero_mem _))

variable (μ : Measure (GA E N)) in

def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E N) where
  carrier := {φ | MemL2Quotient (latticeGL E N) μ φ.1}
  zero_mem' := ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ hγ g => by
    change φ.1 (γ * g) + ψ.1 (γ * g) = φ.1 g + ψ.1 g
    rw [h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩
  smul_mem' := fun c φ h => ⟨fun γ hγ g => by
    change c * φ.1 (γ * g) = c * φ.1 g
    rw [h.1 γ hγ g], h.2.const_smul c⟩

def stabSub (φ : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k φ = φ}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) φ = φ
    have ha' : finRep E N a φ = φ := ha
    have hb' : finRep E N b φ = φ := hb
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change finRep E N 1 φ = φ
    rw [map_one]; rfl
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ φ = φ
    have ha' : finRep E N a φ = φ := ha
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

def typeSub (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) (c : (E →+* ℂ) → ℂ → ℂ) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ) ∧
    ∀ τ u, cap τ u φ = c τ u • φ}
  zero_mem' := ⟨fun _ _ => map_zero _, fun g => by
      have : (fun k : Kinf E N => (cptRep E N k 0).1 g) = 0 := funext fun k => by simp
      rw [this]; exact zero_mem _,
    fun _ _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun k hk => by rw [map_add, h.1 k hk, h'.1 k hk], fun g => by
      have : (fun k : Kinf E N => (cptRep E N k (φ + ψ)).1 g) =
          (fun k : Kinf E N => (cptRep E N k φ).1 g) + (fun k : Kinf E N => (cptRep E N k ψ).1 g) :=
        funext fun k => by simp [map_add]
      rw [this]; exact add_mem (h.2.1 g) (h'.2.1 g),
    fun τ u => by rw [map_add, h.2.2 τ u, h'.2.2 τ u, smul_add]⟩
  smul_mem' := fun a φ h => ⟨fun k hk => by rw [map_smul, h.1 k hk], fun g => by
      have : (fun k : Kinf E N => (cptRep E N k (a • φ)).1 g) = a • (fun k : Kinf E N => (cptRep E N k φ).1 g) :=
        funext fun k => by simp [map_smul]
      rw [this]; exact Submodule.smul_mem _ a (h.2.1 g),
    fun τ u => by rw [map_smul, h.2.2 τ u, smul_comm]⟩

end GlobalTheory.DiscClosure

namespace GlobalTheory.DiscClosure

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx GlobalTheory.DiscLocEx

end GlobalTheory.DiscClosure
