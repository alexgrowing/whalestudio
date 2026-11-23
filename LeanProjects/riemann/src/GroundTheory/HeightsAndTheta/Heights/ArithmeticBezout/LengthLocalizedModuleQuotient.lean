import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace VerticalPartMultiplicity

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)

theorem length_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem length_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

theorem localMult_map_equiv {A B : Type*} [CommRing A] [CommRing B] (Ψ : A ≃+* B) (K W : Ideal A) :
    localMult (K.map (Ψ : A →+* B)) (W.map (Ψ : A →+* B)) = localMult K W := by
  classical
  have hWc : (W.map (Ψ : A →+* B)).comap (Ψ : A →+* B) = W := by
    rw [Ideal.map_comap_of_equiv]
    ext x
    simp [Ideal.mem_comap]
  by_cases hW : W.IsPrime
  · haveI := hW
    haveI hW' : (W.map (Ψ : A →+* B)).IsPrime := Ideal.map_isPrime_of_equiv _
    have H : W.primeCompl.map Ψ.toMonoidHom = (W.map (Ψ : A →+* B)).primeCompl := by
      ext x
      rw [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.map_comap_of_equiv, Ideal.mem_comap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Ideal.mem_primeCompl_iff] at hy
        simpa using hy
      · intro hx
        exact ⟨Ψ.symm x, (Ideal.mem_primeCompl_iff).mpr hx, by simp⟩
    let σ : Localization.AtPrime W ≃+* Localization.AtPrime (W.map (Ψ : A →+* B)) :=
      IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime W)
        (Localization.AtPrime (W.map (Ψ : A →+* B))) Ψ H
    have hIJ : (K.map (Ψ : A →+* B)).map (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))) =
        (K.map (algebraMap A (Localization.AtPrime W))).map (σ : _ →+* _) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      ext x
      exact (IsLocalization.ringEquivOfRingEquiv_eq H x).symm
    let τ := Ideal.quotientEquiv _ _ σ hIJ
    have e1 : Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) =
        Module.length (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W)))
          (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    have e2 : Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)))
        (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
          (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) =
        Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))))
          (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    unfold localMult
    rw [dif_pos hW', dif_pos hW, e1, e2, length_self_eq_of_ringEquiv τ]
  · have hW' : ¬ (W.map (Ψ : A →+* B)).IsPrime := fun h => hW (hWc ▸ Ideal.comap_isPrime _ _)
    unfold localMult
    rw [dif_neg hW', dif_neg hW]

variable {n : ℕ}

def eb (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, i⟩
    rfl

abbrev ι : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm

def Ψ (n : ℕ) : MRing (PBlk n) ≃+* MvPolynomial (Fin n) (𝓞 ℚ) :=
  (renameEquiv ℤ (eb n)).symm.toRingEquiv.trans (mapEquiv (Fin n) ι)

theorem Ψ_apply (f : MRing (PBlk n)) :
    Ψ n f = MvPolynomial.map (ι : ℤ →+* 𝓞 ℚ) (rename (eb n).symm f) := rfl

theorem Ψ_C (a : ℤ) : Ψ n (C a) = C (ι a) := by
  rw [Ψ_apply, rename_C, map_C]
  rfl

theorem Ψ_X (i : Fin n) : Ψ n (X ⟨(), i⟩) = X i := by
  rw [Ψ_apply, rename_X, map_X]
  rfl

theorem Ψ_symm_C (a : 𝓞 ℚ) : (Ψ n).symm (C a) = C (ι.symm a) := by
  rw [RingEquiv.symm_apply_eq, Ψ_C, RingEquiv.apply_symm_apply]

theorem Ψ_symm_X (i : Fin n) : (Ψ n).symm (X i) = X ⟨(), i⟩ := by
  rw [RingEquiv.symm_apply_eq, Ψ_X]

theorem ι_apply (a : ℤ) : ι a = (a : 𝓞 ℚ) := map_intCast ι a

theorem Ψ_linForm (u : Fin n → ℤ) :
    Ψ n (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm (fun j => ((u j : ℤ) : 𝓞 ℚ)) := by
  simp [IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, map_sum, Ψ_C, Ψ_X, ι_apply, Xc]

theorem finIdeal_eq_map (W : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal W =
      W.map ((renameEquiv ℤ (eb n)).symm.toRingEquiv : MRing (PBlk n) →+* MvPolynomial (Fin n) ℤ) := by
  rw [Ideal.map_comap_of_equiv]
  rfl

theorem minimalPrimes_map_equiv {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K : Ideal A) :
    (K.map (Φ : A →+* B)).minimalPrimes = Ideal.map (Φ : A →+* B) '' K.minimalPrimes := by
  have hk : RingHom.ker (Φ : A →+* B) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp Φ.injective
  rw [Ideal.minimalPrimes_map_of_surjective Φ.surjective, hk, sup_bot_eq]

theorem comap_C_map (W : Ideal (MRing (PBlk n))) :
    (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) =
      (W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ) := by
  ext a
  rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, Ideal.mem_comap]
  exact Iff.of_eq (congrArg (· ∈ W) (Ψ_symm_C a))

theorem isHorizontal_iff (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W ↔
      (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = ⊥ := by
  rw [comap_C_map, ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal]
  constructor
  · intro h
    rw [h, Ideal.map_bot]
  · intro h
    exact (Ideal.map_eq_bot_iff_of_injective ι.injective).mp h

theorem isRelevant_map_iff (W : Ideal (MRing (PBlk n))) :
    IsRelevant (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) ↔
      ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    RingEquiv.coe_toRingHom, Ψ_symm_X]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩

theorem localMult_map_eq_multAt (K W : Ideal (MRing (PBlk n))) :
    localMult (K.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
        (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt K W := by
  rw [localMult_map_equiv]
  unfold localMult ReciprocityTheory.ChartRestriction.G.Geo.multAt
  by_cases hW : W.IsPrime
  · rw [dif_pos hW, dif_pos hW]
    haveI := hW
    rw [length_localizedModule_quotient]
  · rw [dif_neg hW, dif_neg hW]

theorem finIdeal_comap_C (P : Ideal (MRing (PBlk n))) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) =
      P.comap (C : ℤ →+* MRing (PBlk n)) := by
  ext a
  simp [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C]

theorem integralModel_genericIdeal (P : Ideal (MRing (PBlk n))) [hP : P.IsPrime]
    (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P) :
    integralModel (genericIdeal P) = P.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by
  set J := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hJdef
  haveI hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hJC : J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) = ⊥ := by
    rw [hJdef, finIdeal_comap_C]
    exact hh
  have key : (J.map (MvPolynomial.map (Int.castRingHom ℚ))).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = J := by
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) :=
      MvPolynomial.algebraMvPolynomial
    haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ))
        (MvPolynomial (Fin n) ℚ) := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors ℤ) ℚ
    have hdisj : Disjoint (((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ) :
        Submonoid (MvPolynomial (Fin n) ℤ)) : Set (MvPolynomial (Fin n) ℤ)) J := by
      refine Set.disjoint_left.mpr fun x hx hxJ => ?_
      obtain ⟨a, ha, rfl⟩ := hx
      have : a ∈ J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) := hxJ
      rw [hJC, Ideal.mem_bot] at this
      exact nonZeroDivisors.ne_zero ha this
    have := IsLocalization.under_map_of_isPrime_disjoint
      ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)) (MvPolynomial (Fin n) ℚ) hJ hdisj
    exact this
  have hm : ∀ f : MvPolynomial (Fin n) (𝓞 ℚ),
      MvPolynomial.map (algebraMap (𝓞 ℚ) ℚ) f =
        MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.map (ι.symm : 𝓞 ℚ →+* ℤ) f) := by
    intro f
    have e : algebraMap (𝓞 ℚ) ℚ = (Int.castRingHom ℚ).comp (ι.symm : 𝓞 ℚ →+* ℤ) := by
      ext z
      simp [Rat.ringOfIntegersEquiv_apply_coe]
    rw [MvPolynomial.map_map, ← e]
  ext f
  rw [integralModel, Ideal.mem_comap, hm, ← Ideal.mem_comap, genericIdeal, ← hJdef, key, hJdef,
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

theorem reduceMod_map (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (W : Ideal (MRing (PBlk n))) :
    reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom v.asIdeal.ResidueField)) := by
  rw [reduceMod, finIdeal_eq_map, Ideal.map_map, Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · simp [Ψ_C, ι_apply]
  · obtain ⟨⟨⟩, i⟩ := p
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [Ψ_X]
    simp [eb]

theorem absNorm_map_comap_C (W : Ideal (MRing (PBlk n))) :
    Ideal.absNorm ((W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing (PBlk n))) with hg
  have hspan : W.comap (C : ℤ →+* MRing (PBlk n)) = Ideal.span {g} :=
    (Ideal.span_singleton_generator _).symm
  rw [hspan, Ideal.map_span, Set.image_singleton, Ideal.absNorm_span_singleton]
  have h1 : (ι : ℤ →+* 𝓞 ℚ) g = algebraMap ℤ (𝓞 ℚ) g :=
    (eq_intCast _ g).trans (eq_intCast _ g).symm
  rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

end VerticalPartMultiplicity

end ObjectsChow

end GroundTheory.Heights₂.Heights
