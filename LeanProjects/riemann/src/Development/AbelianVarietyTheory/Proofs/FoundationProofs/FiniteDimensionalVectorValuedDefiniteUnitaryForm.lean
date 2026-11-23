import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU

theorem finiteDimensional_vecForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let T : M →ₗ[ℂ] (S₀ → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    obtain ⟨hl, hr, hk⟩ := hM f.1 f.2
    have h0 : ∀ s ∈ S₀, ∀ v, f.1 v s = 0 := fun s hs v => LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    apply Subtype.ext
    refine LinearMap.ext fun v => funext fun g => ?_
    obtain ⟨γ, hγ, s, hs, x, hx, k, hkK, rfl⟩ := hS₀ g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := by
      have := congrFun (hk k hkK v) (γ * s * x)
      rw [← this]; rfl
    have e3 : f.1 v (s * x) = f.1 (ρ ⟨x, hx⟩ v) s := by
      rw [hr ⟨x, hx⟩ v]; rfl
    rw [e1, mul_assoc γ s x, hl v γ hγ, e3, h0 s hs]
    rfl
  exact Module.Finite.of_injective T hT

end GlobalTheory.DefU
