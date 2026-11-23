import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameCharaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVectorStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSplitProof

private theorem is_smooth_char_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have hk : (χ⁻¹).ker = χ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  unfold IsSmoothChar
  rw [hk]
  exact h

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  intro hBZ hGL hUP hDZ k _ _ _ _ r t χ π v hχ hT hv hvec

  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hGL hUP hDZ k r t χ π v hχ hT hv hvec
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr ⟨s, d, σ, hsupp, hlt⟩
  ·
    obtain ⟨π₁, π₂, hE, hns⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hGL hUP k r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hGL hDZ k r t χ π π₁ π₂ v hχ hT hns hE hv hvec
    have hχi : IsSmoothChar χ⁻¹ := is_smooth_char_inv hχ
    refine Or.inl ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχi, hsph, ?_⟩
    have h2 := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
    rw [inv_inv] at h2
    show Nonempty (π.π.Equiv (prod₂ π₁.π (twist (twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
    rw [h2]
    exact hE

end GlobalTheory.BlockSplitProof
