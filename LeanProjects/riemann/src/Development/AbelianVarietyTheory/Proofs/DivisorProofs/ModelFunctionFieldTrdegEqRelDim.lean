import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapCompCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Model

theorem trdeg_le_of_isoSquare {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] (a : K →+* L) (b : K' →+* L') (u : K ≃+* K') (v : L ≃+* L')
    (h : b.comp (u : K →+* K') = (v : L →+* L').comp a) :
    @Algebra.trdeg K L _ _ a.toAlgebra ≤ @Algebra.trdeg K' L' _ _ b.toAlgebra := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  unfold Algebra.trdeg
  refine ciSup_le' fun i => ?_
  have hi : AlgebraicIndependent K' (v ∘ ((↑) : i.1 → L)) :=
    (algebraicIndependent_ringHom_iff_of_comp_eq u v v.injective h).mpr i.2
  exact hi.cardinalMk_le_trdeg

theorem trdeg_eq_of_isoSquare {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K] (a : K →+* L) (b : K' →+* L') (u : K ≃+* K') (v : L ≃+* L')
    (h : b.comp (u : K →+* K') = (v : L →+* L').comp a) :
    @Algebra.trdeg K L _ _ a.toAlgebra = @Algebra.trdeg K' L' _ _ b.toAlgebra := by
  haveI : Nontrivial K' := u.injective.nontrivial
  refine le_antisymm (trdeg_le_of_isoSquare a b u v h)
    (trdeg_le_of_isoSquare b a u.symm v.symm ?_)
  ext y
  have := congrArg (fun φ : K →+* L' => φ (u.symm y)) h
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.apply_symm_apply]
    at this
  simp [this]

theorem trdeg_functionField_eq_relDim {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O) :
    letI := (Spec.preimage (Z.X.fromSpecStalk (genericPoint Z.X) ≫ Z.str)).hom.toAlgebra
    Algebra.trdeg O Z.X.functionField = Z.relDim := by
  letI := (Spec.preimage (Z.X.fromSpecStalk (genericPoint Z.X) ≫ Z.str)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_affine_chart_trdeg_eq Z.str (genericPoint Z.X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq Z.str (hA.symm.trans hd)
  have h₂ := topologicalKrullDim_eq_of_isEmbedding Z.gen.ι.isOpenEmbedding.isEmbedding
    (Z := Z.str ⁻¹' {genericPoint (Spec (.of O))}) (by
      rw [Scheme.Opens.range_ι, genericPoint_eq_bot_of_affine]
      ext x
      exact mem_gen_iff_eq_bot.trans
        ⟨fun h => PrimeSpectrum.ext h, fun h => congrArg PrimeSpectrum.asIdeal h⟩)
  rw [h₁, topologicalKrullDim_gen] at h₂
  obtain rfl : d = Z.relDim := by exact_mod_cast h₂
  exact hA.symm.trans hd

theorem fnConst_eq_residue {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O) (g : O) :
    Z.fnConst g = (Z.X.residue (genericPoint Z.X)).hom
      ((Spec.preimage (Z.X.fromSpecStalk (genericPoint Z.X) ≫ Z.str)).hom g) := by
  have n := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of O)).inv g))
    (Scheme.ΓSpecIso_naturality (Spec.preimage (Z.X.fromSpecStalk (genericPoint Z.X) ≫ Z.str)))
  simp only [Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at n
  rw [fnConst, RingHom.comp_apply, const_eq, ← n]
  have hid : (Spec (Z.X.presheaf.stalk (genericPoint Z.X))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (Z.X.presheaf.stalk (genericPoint Z.X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (Z.X.presheaf.stalk (genericPoint Z.X))).Opens) ≤ ⊤))
      = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [hid, CommRingCat.id_apply, Iso.inv_hom_id_apply]
  rfl

theorem trdeg_fnFld_eq_relDim_ofResidue : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O),
    letI := Z.fnConst.toAlgebra; Algebra.trdeg O Z.fnFld = Z.relDim := by
  intro O _ _ _ Z
  have hf : IsField (Z.X.presheaf.stalk (genericPoint Z.X)) := Field.toIsField Z.X.functionField
  letI : Field (Z.X.presheaf.stalk (genericPoint Z.X)) := hf.toField
  have hbij : Function.Bijective (Z.X.residue (genericPoint Z.X)).hom := by
    refine ⟨?_, Ideal.Quotient.mk_surjective⟩
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h0 : a ∈ IsLocalRing.maximalIdeal (Z.X.presheaf.stalk (genericPoint Z.X)) :=
      (IsLocalRing.residue_eq_zero_iff a).1 ha
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h0
  let v := RingEquiv.ofBijective (Z.X.residue (genericPoint Z.X)).hom hbij
  have := trdeg_eq_of_isoSquare
    (Spec.preimage (Z.X.fromSpecStalk (genericPoint Z.X) ≫ Z.str)).hom Z.fnConst
    (RingEquiv.refl O) v (RingHom.ext fun g => (fnConst_eq_residue Z g))
  exact this.symm.trans (trdeg_functionField_eq_relDim Z)

end GlobalTheory.Vert.Model
