import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicCharStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlockStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSph

theorem sph_of_isBlockVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  intro hBZ hG hDZ k _ _ _ _ r t χ π π₁ π₂ v hχ hχt hsupp ⟨φ⟩ hv hblk
  obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd k r t _ _ π₁.π π₂.π
  let Ψ := φ.trans E
  have hsm : IsSmooth (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) :=
    isSmooth_parInd _ _
  have hirr : (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)).IsIrreducible :=
    (MultiIrr.isIrreducible_iff_of_equiv Ψ).1 π.irr
  have hv' : Ψ v ≠ 0 := fun h => hv (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hblk' : IsBlockVec χ (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) (Ψ v) :=
    fun h hh h1 h2 u hu => by
      have := Ψ.toIntertwiningMap.isIntertwining _ _ h v
      rw [hblk h hh h1 h2 u hu, map_smul] at this
      exact this.symm
  obtain ⟨hx0, hx⟩ := GlobalTheory.T.jacquetModule_image_ne_zero_of_blockTypeVector hDZ k r t χ _ _ (Ψ v) hsm hirr hχt hv' hblk'
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy⟩ := GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector _ _ (jac (two (stdSum (rfl : r + t = r + t)))
    (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)))
    {h | ∃ g ∈ KO k (Fin t), h = Pi.mulSingle true g}
    (fun h => (χ (Matrix.GeneralLinearGroup.det (h true)) : ℂ)) _ hx0
    (by rintro _ ⟨g, hg, rfl⟩; simpa using hx g hg)
  have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact π₁.smooth
    · exact π₂.smooth
  have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact hasFiniteLength_of_isIrreducible π₁.irr
    · exact hasFiniteLength_of_isIrreducible π₂.irr
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ hsub
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (g j) fun i => (s i j).ρ)
    Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0
    (fun h hh => by simpa using hy (Pi.mulSingle true h) ⟨h, hh, rfl⟩)
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity k Bool (fun i => Fin (b.1 i true)) (Fin t) (g true) _ (fun i => (s i true).ρ) χ z hz0 hz
  by_cases hm : b.1 false true = 0
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) true χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw true)
    have hc : b.1 true false = 0 := by
      have h1 := b.2.1 true
      have h2 := b.2.2 true
      simp [Fintype.sum_bool] at h1 h2
      omega
    exact GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block k t _ π₂.π (b.1 true) (f true) (s true) χ z' π₂.smooth π₂.irr hc (hrow true) hz'0 hz'
  · obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) false χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
    obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hDZ k _ _ (s false true).ρ χ z' (s false true).smooth (s false true).irr hχ
      (Nat.pos_of_ne_zero hm) hz'0 hz'
    exact absurd (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG k r _ π₁.π Bool (b.1 false) (f false) (s false) true _ π₁.smooth (hrow false) hα) (hsupp α)

end GlobalTheory.BlockSph
