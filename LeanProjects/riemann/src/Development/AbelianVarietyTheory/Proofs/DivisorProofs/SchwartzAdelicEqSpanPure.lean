import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylSpan

theorem pure_eq_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F (⇑f) (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := by
  rfl

theorem schA_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  intro F _ _ κ _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, g, hg, rfl⟩
    let L : ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
      { toFun := fun g => pureA F (⇑f) g
        map_add' := fun a b => by funext x; simp [pureA, mul_add]
        map_smul' := fun c a => by funext x; simp [pureA]; ring }
    have h := GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg
    have h2 : L g ∈ Submodule.map L (Submodule.span ℂ _) := Submodule.mem_map_of_mem h
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨φ, hφ, hcof, rfl⟩, rfl⟩
    exact ⟨f, φ, hφ, hcof, (pure_eq_pureA f φ).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, hφ, hcof, rfl⟩
    refine Submodule.subset_span ⟨f, _, ?_, pure_eq_pureA f φ⟩
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩

end GlobalTheory.WeylSpan

end
