import Mathlib
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreIncompTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter.PointVertical

namespace FibreIncompressibility

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in

theorem card_add_card_forgottenBlocks [Fintype K] {κ : K → K'} (hκ : Function.Injective κ) :
    Fintype.card K + Fintype.card (FibreBlock κ) = Fintype.card K' := by
  classical
  have h1 := Fintype.card_subtype_compl (fun k' => k' ∈ Set.range κ)
  have h2 : Fintype.card {k' // k' ∈ Set.range κ} = Fintype.card K := Set.card_range_of_injective hκ
  have h3 := Fintype.card_subtype_le (fun k' => k' ∈ Set.range κ)
  have h4 : Fintype.card (FibreBlock κ) = Fintype.card {k' // ¬ k' ∈ Set.range κ} :=
    Fintype.card_congr (Equiv.refl _)
  omega

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem algebraMap_injective_of_horizontal (I : Ideal (MRing ι)) (h : IsHorizontal I) :
    Function.Injective (algebraMap ℤ (MRing ι ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* MRing ι) := ha
  rw [h] at h'
  exact h'

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem comap_C_imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    (imageZ v W').comap (C : ℤ →+* MRing ι) = W'.comap (C : ℤ →+* MRing ι') := by
  ext a
  simp [imageZ, Ideal.mem_comap]

theorem dim_add_card_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W' : Ideal (MRing ι')} (hW' : IsMultiProjPrime W') :
    ringKrullDim (MRing ι ⧸ imageZ v W') + (Fintype.card (FibreBlock κ) : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι' ⧸ W') := by
  classical
  have := hW'.1
  have : (imageZ v W').IsPrime := Ideal.comap_isPrime _ _
  by_cases hh : IsHorizontal W'
  · have hh' : IsHorizontal (imageZ v W') := by
      unfold IsHorizontal
      rw [comap_C_imageZ]
      exact hh
    have hD := IntDomainDim.proof (MRing ι' ⧸ W') (algebraMap_injective_of_horizontal W' hh)
    have hC := IntDomainDim.proof (MRing ι ⧸ imageZ v W') (algebraMap_injective_of_horizontal _ hh')
    have ht := trdeg_add_card_le (S := ℤ) hv W' hW'.2.1 hW'.2.2 (algebraMap_injective_of_horizontal _ hh')
    have ht' : Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ imageZ v W')) + Fintype.card (FibreBlock κ) ≤
        Cardinal.toENat (Algebra.trdeg ℤ (MRing ι' ⧸ W')) := by
      have := OrderHomClass.mono Cardinal.toENat ht
      rw [map_add, Cardinal.toENat_nat] at this
      exact this
    rw [hD, hC]
    have h2 : Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ imageZ v W')) + 1 + Fintype.card (FibreBlock κ) ≤
        Cardinal.toENat (Algebra.trdeg ℤ (MRing ι' ⧸ W')) + 1 := by
      rw [add_right_comm]
      gcongr
    exact_mod_cast h2
  · have hpr := charOf_prime hW'.1 hh
    set p := charOf W' with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have hp' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
    have hp : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
      show rename v ((p : ℕ) : MRing ι) ∈ W'
      simpa using hp'
    have hV := isMultiProjPrime_red p hW' hp'
    have := hV.1
    set V := W'.map (red p) with hVdef
    have : (V.comap (rename v : MRingOver (ZMod p) ι →ₐ[ZMod p] MRingOver (ZMod p) ι').toRingHom).IsPrime :=
      Ideal.comap_isPrime _ _
    have hinj : Function.Injective (algebraMap (ZMod p)
        (MRingOver (ZMod p) ι ⧸ V.comap (rename v : MRingOver (ZMod p) ι →ₐ[ZMod p] MRingOver (ZMod p) ι').toRingHom)) :=
      (algebraMap (ZMod p) _).injective
    have ht := trdeg_add_card_le (S := ZMod p) hv V hV.2.1 hV.2.2 hinj
    have : Algebra.FiniteType (ZMod p) (MRingOver (ZMod p) ι' ⧸ V) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (ZMod p) V) (Ideal.Quotient.mkₐ_surjective (ZMod p) V)
    have : Algebra.FiniteType (ZMod p)
        (MRingOver (ZMod p) ι ⧸ V.comap (rename v : MRingOver (ZMod p) ι →ₐ[ZMod p] MRingOver (ZMod p) ι').toRingHom) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (ZMod p) _) (Ideal.Quotient.mkₐ_surjective (ZMod p) _)
    obtain ⟨sD, hsD1, hsD2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MRingOver (ZMod p) ι' ⧸ V)
    obtain ⟨sC, hsC1, hsC2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p)
      (A := MRingOver (ZMod p) ι ⧸ V.comap (rename v : MRingOver (ZMod p) ι →ₐ[ZMod p] MRingOver (ZMod p) ι').toRingHom)
    rw [hsD2, hsC2] at ht
    have hle : sC + Fintype.card (FibreBlock κ) ≤ sD := by exact_mod_cast ht
    have hDdim : ringKrullDim (MRing ι' ⧸ W') = sD := by rw [← ringKrullDim_red p hp', hsD1]
    have hCdim : ringKrullDim (MRing ι ⧸ imageZ v W') = sC := by
      rw [← ringKrullDim_red p hp, ← imageVar_red p v hp']
      exact hsC1
    rw [hDdim, hCdim]
    exact_mod_cast hle

end FibreIncompressibility

open FibreIncompressibility in

theorem FibreIncomp.full : Inter.FibreIncomp.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW W₁ W₂ hW₁ hW₂ h12
  classical
  by_contra hne
  obtain ⟨f, hf2, hf1⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h12 hne)
  have := hP'.2.1.1
  have := hW₁.1.1
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hs1 : rename v s ∈ W₁ := by
    have h : s ∈ imageZ v W₁ := hW₁.2.2 ▸ hsW
    exact h
  have hsP : rename v s ∉ P' := hsQ
  have hB : ringKrullDim (MRing ι' ⧸ W₁) + 1 ≤ ringKrullDim (MRing ι' ⧸ P') :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hW₁.2.1) (Ideal.Quotient.factor_surjective _)
      (r := Ideal.Quotient.mk P' (rename v s))
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hs1)
  have h21 : ringKrullDim (MRing ι' ⧸ W₂) + 1 ≤ ringKrullDim (MRing ι' ⧸ W₁) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h12) (Ideal.Quotient.factor_surjective _)
      (r := Ideal.Quotient.mk W₁ f)
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hf2)
  have hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsQ⟩
  have hA := divSuppArith K ι (imageZ v P') n _ _ W hQ hsec hW
  have hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    by_cases hh : IsHorizontal W
    · exact (hA.1 hh).2.2.2
    · exact (hA.2 hh).2.2
  have hlow := dim_add_card_le hv hW₂.1
  rw [hW₂.2.2, hdW] at hlow
  rw [hP'.2.2.2] at hB
  have hcard := card_add_card_forgottenBlocks hv.1
  have hchain : ((n + Fintype.card K + Fintype.card (FibreBlock κ) + 1 + 1 : ℕ) : WithBot ℕ∞) ≤
      ((n + 1 + Fintype.card K' : ℕ) : WithBot ℕ∞) := by
    calc ((n + Fintype.card K + Fintype.card (FibreBlock κ) + 1 + 1 : ℕ) : WithBot ℕ∞)
        = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) + (Fintype.card (FibreBlock κ) : WithBot ℕ∞) + 1 + 1 := by
          push_cast
          rfl
      _ ≤ ringKrullDim (MRing ι' ⧸ W₂) + 1 + 1 := by gcongr
      _ ≤ ringKrullDim (MRing ι' ⧸ W₁) + 1 := by gcongr
      _ ≤ _ := hB
  have : n + Fintype.card K + Fintype.card (FibreBlock κ) + 1 + 1 ≤ n + 1 + Fintype.card K' := by
    exact_mod_cast hchain
  omega

end GroundTheory.Heights₂.Heights.ForSecondHalf
