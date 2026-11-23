import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import Development.WeilBound.CoreStatements.IdealCycleValues.FlatColon
import Development.WeilBound.CoreStatements.IdealCycleValues.OfIdealCycleNe

namespace BaseChangeColon.BC

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] {ϖ : O} {ϖ' : O'} {u : O'ˣ} {e : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDiscreteValuationRing O'] in
theorem mem_of_mem {σ : Type} (he : 0 < e) (h : algebraMap O O' ϖ = u * ϖ' ^ e)
    (W : Ideal (MvPolynomial σ O')) (hW : C ϖ' ∈ W) :
    MvPolynomial.map (algebraMap O O') (C ϖ) ∈ W := by
  rw [map_C, h, C_mul, C_pow]
  exact W.mul_mem_left _ (W.pow_mem_of_mem hW e he)

omit [IsDiscreteValuationRing O'] in
theorem flat_of (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (h : algebraMap O O' ϖ = u * ϖ' ^ e) :
    Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow, h] at ha
    exact mul_ne_zero (v.isUnit.map (algebraMap O O')).ne_zero
      (pow_ne_zero n (mul_ne_zero u.ne_zero (pow_ne_zero e hϖ'.ne_zero))) ha
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  infer_instance

theorem local_of (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) : IsLocalHom (algebraMap O O') := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  have h1 : a ∈ IsLocalRing.maximalIdeal O := h0
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul, h] at ha
  exact hϖ'.not_isUnit ((isUnit_pow_iff he.ne').1
    (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right ha)))

theorem bc_vert (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (bs : Fin d → K → ℤ) (J : Ideal (MRing ι O))
    (hJ : IsMultiHomogIdeal J) (hJ' : IsMultiHomogIdeal (J.map (MvPolynomial.map (algebraMap O O'))))
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hd' : ringKrullDim (MRing ι O' ⧸ J.map (MvPolynomial.map (algebraMap O O'))) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) (hm : C ϖ ∈ J) :
    NN (J.map (MvPolynomial.map (algebraMap O O'))) bs = e * NN J bs := by
  have := local_of hϖ hϖ' he h
  have hmax : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal O
  have h1 : (C ϖ' ^ e : MRing ι O') ∈ J.map (MvPolynomial.map (algebraMap O O')) := by
    have h2 := Ideal.mul_mem_left _ (C (↑u⁻¹ : O'))
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap O O')) hm)
    rwa [map_C, h, ← C_mul, Units.inv_mul_cancel_left, C_pow] at h2
  rw [NN_pow hϖ' hJ' hd' e h1
      (fun k hk g hg => ram_colon ϖ hmax ϖ' hϖ'.ne_zero u e k h hk J hm g hg) bs,
    NN_vert hϖ' (SupSpanMultiHomog.proof O' K ι _ _ 0 hJ' (homog_C ϖ'))
      ((dim_mono le_sup_left).trans_lt hd')
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) bs,
    special_sup hϖ', NN_vert hϖ hJ hd hm bs]
  congr 1
  rw [← ((GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 (IsLocalRing.ResidueField O)
    (IsLocalRing.ResidueField O') K ι (specialIdeal J)).2 d bs)]
  congr 1
  unfold specialIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, map_map]
  rfl

theorem bc_all (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (bs : Fin d → K → ℤ) (J : Ideal (MRing ι O)) :
    IsMultiHomogIdeal J → IsMultiHomogIdeal (J.map (MvPolynomial.map (algebraMap O O'))) →
    ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ringKrullDim (MRing ι O' ⧸ J.map (MvPolynomial.map (algebraMap O O'))) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    NN (J.map (MvPolynomial.map (algebraMap O O'))) bs = e * NN J bs := by
  have := flat_of hϖ hϖ' h
  induction J using IsNoetherian.induction with
  | hgt J ih =>
    intro hJ hJ' hd hd'
    have hcol := map_colon (O' := O') J (C ϖ)
    have hC : IsMultiHomog (MvPolynomial.map (algebraMap O O') (C ϖ : MRing ι O)) 0 := by
      rw [map_C]; exact homog_C _
    by_cases hc : J.colon {C ϖ} = J
    · rw [hc] at hcol
      rw [NN_nzd hϖ hJ hd (C ϖ) (fun _ hW => hW) hc bs,
        NN_nzd hϖ' hJ' hd' _ (mem_of_mem he h) hcol bs, mul_zero]
    · have hsup : Ideal.map (MvPolynomial.map (algebraMap O O')) (J ⊔ Ideal.span {C ϖ}) =
          Ideal.map (MvPolynomial.map (algebraMap O O')) J ⊔
            Ideal.span {MvPolynomial.map (algebraMap O O') (C ϖ : MRing ι O)} := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      have h1 := ih (J.colon {C ϖ}) (lt_of_le_of_ne (le_colon J _) (Ne.symm hc))
        (ColonMultiHomog.full O K ι J _ 0 hJ (homog_C ϖ))
        (hcol ▸ ColonMultiHomog.full O' K ι _ _ 0 hJ' hC)
        ((dim_mono (le_colon J _)).trans_lt hd)
        ((dim_mono (Ideal.map_mono (le_colon J _))).trans_lt hd')
      have h2 := bc_vert hϖ hϖ' he h bs (J ⊔ Ideal.span {C ϖ})
        (SupSpanMultiHomog.proof O K ι J _ 0 hJ (homog_C ϖ))
        (hsup ▸ SupSpanMultiHomog.proof O' K ι _ _ 0 hJ' hC)
        ((dim_mono le_sup_left).trans_lt hd)
        ((dim_mono (Ideal.map_mono le_sup_left)).trans_lt hd')
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [NN_add hϖ' hJ' hd' hC bs, NN_add hϖ hJ hd (homog_C ϖ) bs, hcol, ← hsup, h1, h2, mul_add]

theorem bc_div (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (P : Ideal (MRing ι O)) (hP : IsModelOver P d)
    (hP' : IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d) (a : K → ℕ) (f : MRing ι O)
    (hf : IsMultiHomog f a) (hfP : f ∉ P) (bs : Fin d → K → ℤ) :
    NN (P.map (MvPolynomial.map (algebraMap O O')) ⊔
      Ideal.span {MvPolynomial.map (algebraMap O O') f}) bs = e * NN (P ⊔ Ideal.span {f}) bs := by
  have := flat_of hϖ hϖ' h
  have hf' : IsMultiHomog (MvPolynomial.map (algebraMap O O') f) a := fun m hm =>
    hf (d := m) fun h0 => hm (by rw [coeff_map, h0, map_zero])
  have hc : P.colon {f} = P := by
    refine le_antisymm (fun y hy => ?_) (le_colon P f)
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    exact (hP.multiProj.isPrime.mem_or_mem hy).resolve_right hfP
  have hcol := map_colon (O' := O') P f
  rw [hc] at hcol
  have hfP' : MvPolynomial.map (algebraMap O O') f ∉ P.map (MvPolynomial.map (algebraMap O O')) := by
    intro h0
    apply hP'.multiProj.isPrime.ne_top
    rw [← hcol, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, one_smul]
    exact h0
  have hsup : (P ⊔ Ideal.span {f}).map (MvPolynomial.map (algebraMap O O')) =
      P.map (MvPolynomial.map (algebraMap O O')) ⊔
        Ideal.span {MvPolynomial.map (algebraMap O O') f} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h1 := bc_all hϖ hϖ' he h bs (P ⊔ Ideal.span {f})
    (SupSpanMultiHomog.proof O K ι P f a hP.multiProj.multiHomog hf)
    (hsup ▸ SupSpanMultiHomog.proof O' K ι _ _ a hP'.multiProj.multiHomog hf')
    (withBotENat_lt_of_add_one_le (hP.dim ▸ dim_drop hP.multiProj.isPrime hfP))
    (hsup ▸ withBotENat_lt_of_add_one_le (hP'.dim ▸ dim_drop hP'.multiProj.isPrime hfP'))
  rwa [hsup] at h1

end BaseChangeColon.BC

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem BaseChangeColon.isModelOver_ramified_base_change : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  intro O O' _ _ _ _ _ _ _ ϖ ϖ' u e hϖ hϖ' he h K _ _ J _ P d hP hP' a f hf hfP l hl
  subst hl
  exact BaseChangeColon.BC.bc_div hϖ hϖ' he h P hP hP' a f hf hfP l.get
