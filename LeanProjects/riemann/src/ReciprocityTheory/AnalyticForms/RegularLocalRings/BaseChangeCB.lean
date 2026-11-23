import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R.BaseChangeC

open MvPolynomial TensorProduct

variable {σ : Type} [Fintype σ]

noncomputable def quotExtEquiv (𝔭 : Ideal (MvPolynomial σ ℚ)) :
    (ℂ ⊗[ℚ] (MvPolynomial σ ℚ ⧸ 𝔭)) ≃+* (MvPolynomial σ ℂ ⧸ Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ℚ) ℂ (MvPolynomial σ ℚ) ℂ 𝔭).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (algebraTensorAlgEquiv ℚ ℂ).toRingEquiv (by
      have h : (algebraTensorAlgEquiv (σ := σ) ℚ ℂ).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : MvPolynomial σ ℚ →ₐ[ℚ] ℂ ⊗[ℚ] MvPolynomial σ ℚ).toRingHom
          = MvPolynomial.map (algebraMap ℚ ℂ) := by
        apply RingHom.ext
        intro p
        simp [Algebra.TensorProduct.includeRight_apply, algebraTensorAlgEquiv_tmul]
      rw [← h, ← Ideal.map_map]
      rfl))

section Rad

theorem isRadical_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  set A := MvPolynomial σ ℚ ⧸ 𝔭
  set K := FractionRing A
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have h3 : IsReduced (ℂ ⊗[ℚ] A) := isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)).toRingHom hinj
  exact isReduced_of_injective (quotExtEquiv 𝔭).symm.toRingHom (quotExtEquiv 𝔭).symm.injective

end Rad

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem flat_mvPolynomial_rat_complex :
    Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℚ (MvPolynomial σ ℚ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℚ) (S := MvPolynomial σ ℚ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem comap_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have hQp : Q.IsPrime := hQ.1.1
  have hle : Ideal.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) 𝔭 ≤ Q := hQ.1.2
  set q := Q.comap (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) with hq
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
  have hPext : Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭 ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
  have hPQe : P = Q := le_antisymm hPQ hQP
  subst hPQe
  exact hPl.over.symm

theorem height_eq_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have : Q.IsPrime := hQ.1.1
  have hc := comap_of_mem_minimalPrimes_map 𝔭 Q hQ
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))))).height = 0 := by
    have hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))).minimalPrimes := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]

end GD

theorem height_add_ringKrullDim_quotient_fintype (k : Type) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by
  let e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k :=
    (MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv
  have : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)
  rw [RingEquiv.height_map,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)] at h
  exact h

theorem withBot_enat_cancel {h : ℕ∞} {a b : WithBot ℕ∞} {N : ℕ}
    (ha : (h : WithBot ℕ∞) + a = N) (hb : (h : WithBot ℕ∞) + b = N) : a = b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hb
    | coe b =>
      have ha' : h + a = N := by exact_mod_cast ha
      have hb' : h + b = N := by exact_mod_cast hb
      congr 1
      induction h using ENat.recTopCoe with
      | top => simp at ha'
      | coe h => exact WithTop.add_left_cancel (ENat.coe_ne_top h) (ha'.trans hb'.symm)

theorem ringKrullDim_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R.BaseChangeC
