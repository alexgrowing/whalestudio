import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFiniteAdeleLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFiniteLocalApproxThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalActionAtSpecialPlaceStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TrFin

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T (0 : (κ → Fv F v) → ℂ) 0 := by
  intro r _
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 := by funext x; simp [tens]
  rw [e, map_zero]

theorem transfer {P M M' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup M] [Module ℂ M] [AddCommGroup M']
    [Module ℂ M'] (S : Submodule ℂ M) (S' : Submodule ℂ M') (p : M →ₗ[ℂ] P) (p' : M' →ₗ[ℂ] P) (A : M → M → Prop)
    (A' : M' → M' → Prop) (onto : S.map p = ⊤) (ex : ∀ φ ∈ S, ∃ φ₁ ∈ S, A φ φ₁)
    (lin : ∀ φ ∈ S, ∀ ψ ∈ S, ∀ φ₁ ψ₁, A φ φ₁ → A ψ ψ₁ → ∀ a b : ℂ, A (a • φ + b • ψ) (a • φ₁ + b • ψ₁))
    (z' : A' 0 0)
    (eqv : ∀ φ ∈ S, ∀ φ' ∈ S', ∀ φ₁ ∈ S, ∀ φ₁' ∈ S', A φ φ₁ → A' φ' φ₁' → p φ = p' φ' → p φ₁ = p' φ₁') :
    ∃ L : P →ₗ[ℂ] P, (∀ φ ∈ S, ∀ φ₁ ∈ S, A φ φ₁ → L (p φ) = p φ₁) ∧
      (∀ φ' ∈ S', ∀ φ₁' ∈ S', A' φ' φ₁' → L (p' φ') = p' φ₁') := by
  classical
  have key : ∀ φ ∈ S, ∀ φ₁ ∈ S, A φ φ₁ → p φ = 0 → p φ₁ = 0 := fun φ hφ φ₁ hφ₁ hA h0 => by
    have := eqv φ hφ 0 S'.zero_mem φ₁ hφ₁ 0 S'.zero_mem hA z' (by rw [h0, map_zero])
    rwa [map_zero] at this
  have uniq : ∀ φ ∈ S, ∀ ψ ∈ S, ∀ φ₁ ∈ S, ∀ ψ₁ ∈ S, A φ φ₁ → A ψ ψ₁ → p φ = p ψ → p φ₁ = p ψ₁ := by
    intro φ hφ ψ hψ φ₁ hφ₁ ψ₁ hψ₁ hA hB he
    have h := lin φ hφ ψ hψ φ₁ ψ₁ hA hB 1 (-1)
    have := key _ (S.add_mem (S.smul_mem 1 hφ) (S.smul_mem (-1) hψ)) _
      (S.add_mem (S.smul_mem 1 hφ₁) (S.smul_mem (-1) hψ₁)) h (by simp [he])
    have e : p ((1 : ℂ) • φ₁ + (-1 : ℂ) • ψ₁) = p φ₁ - p ψ₁ := by simp [sub_eq_add_neg]
    rw [e] at this
    exact sub_eq_zero.1 this
  let q := p.domRestrict S
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, LinearMap.range_domRestrict, onto]
  let c : S → M := fun φ => (ex φ.1 φ.2).choose
  have hc : ∀ φ : S, c φ ∈ S ∧ A φ.1 (c φ) := fun φ => (ex φ.1 φ.2).choose_spec
  let g : S →ₗ[ℂ] P :=
    { toFun := fun φ => p (c φ)
      map_add' := fun φ ψ => by
        rw [← map_add]
        have h := lin _ φ.2 _ ψ.2 _ _ (hc φ).2 (hc ψ).2 1 1
        simp only [one_smul] at h
        exact uniq _ (φ + ψ).2 _ (φ + ψ).2 _ (hc _).1 _ (S.add_mem (hc φ).1 (hc ψ).1) (hc _).2 h rfl
      map_smul' := fun a φ => by
        rw [RingHom.id_apply, ← map_smul]
        have h := lin _ φ.2 _ φ.2 _ _ (hc φ).2 (hc φ).2 a 0
        simp only [zero_smul, add_zero] at h
        exact uniq _ (a • φ).2 _ (a • φ).2 _ (hc _).1 _ (S.smul_mem a (hc φ).1) (hc _).2 h rfl }
  have hker : LinearMap.ker q ≤ LinearMap.ker g := fun φ hφ => by
    rw [LinearMap.mem_ker] at hφ ⊢
    exact key _ φ.2 _ (hc φ).1 (hc φ).2 hφ
  let L : P →ₗ[ℂ] P :=
    ((LinearMap.ker q).liftQ g hker).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hL : ∀ φ : S, L (p φ) = p (c φ) := fun φ => by
    have e : (q.quotKerEquivOfSurjective hq).symm (q φ) = Submodule.Quotient.mk φ := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker q).liftQ g hker ((q.quotKerEquivOfSurjective hq).symm (q φ)) = _
    rw [e, Submodule.liftQ_apply]; rfl
  refine ⟨L, fun φ hφ φ₁ hφ₁ hA => ?_, fun φ' hφ' φ₁' hφ₁' hA' => ?_⟩
  · rw [hL ⟨φ, hφ⟩]
    exact uniq φ hφ φ hφ _ (hc _).1 φ₁ hφ₁ (hc ⟨φ, hφ⟩).2 hA rfl
  · obtain ⟨φ, hφ, he⟩ : ∃ φ ∈ S, p φ = p' φ' := by
      have : p' φ' ∈ S.map p := by rw [onto]; trivial
      obtain ⟨φ, hφ, he⟩ := this
      exact ⟨φ, hφ, he⟩
    rw [← he, hL ⟨φ, hφ⟩]
    exact eqv φ hφ φ' hφ' _ (hc _).1 φ₁' hφ₁' (hc ⟨φ, hφ⟩).2 hA' he

end GlobalTheory.TrFin

namespace GlobalTheory.TrFin

end GlobalTheory.TrFin

end
