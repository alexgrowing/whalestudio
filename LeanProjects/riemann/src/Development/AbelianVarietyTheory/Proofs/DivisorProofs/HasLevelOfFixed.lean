import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductEqFinprodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTracesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfFixedVectorsAdelicLevelNeBotOfLocalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelFormsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isCompU_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {w : Pl E} {σ σ' : SmIrr (UL n w)}
    (h : IsCompU π w σ) (e : σ.ρ.Equiv σ'.ρ) : IsCompU π w σ' := by
  obtain ⟨p, hp, -, f, hf0, hfπ, hfe⟩ := h
  let g : σ'.V →ₗ[ℂ] σ.V := e.symm.toLinearEquiv.toLinearMap
  have hg : ∀ x v, g (σ'.ρ x v) = σ.ρ x (g v) := fun x v =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) v
  refine ⟨p, hp, σ'.irred, f ∘ₗ g, ?_, fun v => hfπ _, fun x v => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (e.toLinearEquiv v)
    simpa [g] using this
  · simp only [LinearMap.comp_apply, hg, hfe]

theorem hasLevel_of_fixed {S : Set (Pl E)} (hS : IsSection S) {π : Submodule ℂ (UA E n → ℂ)}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (h : π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) : HasLevel S π K' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨φ, (Submodule.mem_inf.1 hφ).1, hφ0, fun w hw x hx hk => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hk
  have hxf : x ∈ finU E n := hx.1
  have hmem : (⟨x, hxf⟩ : finU E n) ∈ globLev S K' := by
    simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map]
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      exact ⟨k, hk, hkx⟩
    · have hu : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        intro he
        exact hww ((hS w).unique ⟨hw', he⟩ ⟨hw, rfl⟩)
      have hker : x ∈ (cLoc w').ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 w') hu
      refine ⟨1, one_mem _, ?_⟩
      simpa using (MonoidHom.mem_ker.1 hker).symm
  have := (Submodule.mem_inf.1 hφ).2 ⟨_, hmem⟩
  simpa [fixed, eig, RF] using this

theorem dimW_ne_zero (lam : InfinitePlace E → DomWeight n) : dimW lam ≠ 0 := by
  unfold dimW
  rw [Finset.prod_ne_zero_iff]
  intro v _
  rw [map_one, LinearMap.trace_one]
  exact_mod_cast Module.finrank_pos.ne'

end GlobalTheory.BCT
