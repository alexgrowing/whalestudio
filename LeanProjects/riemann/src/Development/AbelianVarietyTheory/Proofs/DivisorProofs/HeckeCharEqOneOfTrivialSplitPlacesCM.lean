import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMDblR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModuloStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartEqOneMulInvMemSplitCongruenceIdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOneStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.HeckeSplitGen

theorem heckeChar_eq_one_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 → ν x = 1) →
      ∀ x, ν x = 1 := by
  intro F E _ _ _ _ _ σ hcm ν hν hs
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.unitaryIdeleChar_trivial_congruentOneModulo F E ν hν.1
  have hH : grpHF σ N ≤ ν.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ((⟨k, rfl⟩ | ⟨e, he, hx⟩) | hx)
    · exact hν.2 k
    · exact hs e he x hx
    · exact hA x hx
  have hcl : closure (grpHF σ N : Set (AF F ⊗[F] E)ˣ) ⊆ ν.ker := by
    refine closure_minimal hH ?_
    have : (ν.ker : Set (AF F ⊗[F] E)ˣ) = ν ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hν.1
  intro x
  obtain ⟨z, hz, hxz⟩ := GlobalTheory.T.exists_finPart_eq_one_mul_inv_mem_split_congruence_ideles F E σ hcm N hN x
  have h1 : ν (x * z⁻¹) = 1 := hH hxz
  have h2 : ν z = 1 := hcl (GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one F E σ hcm N hN z hz)
  have : x = x * z⁻¹ * z := by group
  rw [this, map_mul, h1, h2, one_mul]

end GlobalTheory.HeckeSplitGen

end
