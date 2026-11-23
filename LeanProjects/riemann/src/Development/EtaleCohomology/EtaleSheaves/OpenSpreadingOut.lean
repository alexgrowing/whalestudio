import Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut Topology

namespace LateralTheory.E.OpenSpreadingOut

lemma toR_apply_bot {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (toR R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R Ω)

theorem etale_open_spreading_out_over_finitely_generated_subalgebra : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread := by
  intro k _ Ω _ _ R hR C A c p v U hp sq hU
  obtain ⟨hfp, hqc, hqs⟩ := hp
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : LocallyOfFiniteType p := inferInstance
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian A := {}
  have hZ : IsConstructible ((U : Set A)ᶜ) := by
    rw [isConstructible_compl]
    exact IsRetrocompact.isConstructible U.isOpen
      (fun W _ _ => TopologicalSpace.NoetherianSpace.isCompact _)
  have hI : IsConstructible (p '' (U : Set A)ᶜ) := p.isConstructible_image hZ
  have hT : IsConstructible (p '' (U : Set A)ᶜ)ᶜ := isConstructible_compl.mpr hI
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ (p '' (U : Set A)ᶜ)ᶜ := by
    rintro ⟨a, ha, hpa⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := toR R) a
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) (by rw [hpa, toR_apply_bot])
    apply ha
    have := hU (sq.isoPullback.inv z)
    rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz] at this
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem hT hη
  have hs' : (s : Ω) ≠ 0 := fun h => hs0 (Subtype.ext h)
  refine ⟨R ⊔ Algebra.adjoin k {(s : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(s : Ω)⁻¹}, by simp⟩, ?_⟩
  intro R' hSR' hRR' E q' r sq' z
  by_contra hz
  have hw : p (r z) = (incl hRR') (q' z) := by
    rw [← Scheme.Hom.comp_apply, sq'.w, Scheme.Hom.comp_apply]
  have hmem := hs ((incl hRR') (q' z)) ?_
  · exact hmem ⟨r z, hz, hw⟩
  · intro hsp
    change Subalgebra.inclusion hRR' s ∈ (q' z).asIdeal at hsp
    have hinv : (s : Ω)⁻¹ ∈ R' := hSR' (le_sup_right (a := R) (Algebra.subset_adjoin rfl))
    have hu : IsUnit (Subalgebra.inclusion hRR' s) :=
      IsUnit.of_mul_eq_one ⟨(s : Ω)⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hs'))
    exact (q' z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp hu)

end LateralTheory.E.OpenSpreadingOut

end
