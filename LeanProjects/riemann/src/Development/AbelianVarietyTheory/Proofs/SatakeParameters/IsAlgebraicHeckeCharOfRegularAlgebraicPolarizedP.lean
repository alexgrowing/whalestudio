import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRealSubfieldAlgebraicOfCompNormIntegralStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.RegAlgCharAlg

theorem expo_mul' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ χ' : HChar E) (τ : E →+* ℂ) :
    expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (τ : E →+* ℂ) :
    expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul' χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isAlgPos_of_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ →
      ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ a ha π χ hreg hpol
  refine GlobalTheory.T.heckeChar_realSubfield_algebraic_of_comp_norm_integral E χ fun τ => ?_
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ
  have h1 := (hm τ).twist ψ⁻¹
  have key := GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (NumberField.ComplexEmbedding.conjugate τ))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
  obtain ⟨n, hn⟩ := (hreg τ).2 z hz
  have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) := by
    rw [key, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
  refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
  rw [expo_inv'] at hn'
  push_cast
  linear_combination hn' + hn

end GlobalTheory.RegAlgCharAlg
