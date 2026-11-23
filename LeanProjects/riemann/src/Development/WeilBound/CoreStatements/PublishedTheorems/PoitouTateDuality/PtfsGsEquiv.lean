import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NSEqFixingSubgroup

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

theorem gsEquiv_toGS' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∃ e : GS (AlgebraicClosure ℚ) S ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) S,
      ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S),
        ((e (toGS (AlgebraicClosure ℚ) S σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          σ (y : AlgebraicClosure ℚ) := by
  have : IsGalois K (AlgebraicClosure ℚ) := IsAlgClosure.isGalois K (AlgebraicClosure ℚ)
  let E := maxUnramifiedOutside K (AlgebraicClosure ℚ) S
  let φ : G K (AlgebraicClosure ℚ) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)
  have hker : φ.ker = NS (AlgebraicClosure ℚ) S := by
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.NS_eq_fixingSubgroup K (AlgebraicClosure ℚ) S]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS (AlgebraicClosure ℚ) S ≃* Gal(E/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G K (AlgebraicClosure ℚ)) := inferInstance
  have : CompactSpace (GS (AlgebraicClosure ℚ) S) := Quotient.compactSpace
  refine ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq },
    fun σ y => ?_⟩
  exact AlgEquiv.restrictNormal_commutes σ E y

end PositivityTheory.Lit1.PTN
