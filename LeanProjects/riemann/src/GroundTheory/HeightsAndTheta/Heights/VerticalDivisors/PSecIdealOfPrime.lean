import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecIdealOfPrime
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecIdealOfPrime

theorem secAlg_of_ratFunc {k E : Type} [Field k] [Field E] (n e : ℕ) (φ : k →+* E) (y : Par e n → E)
    (hinj : Function.Injective (eval₂Hom φ y))
    (hsurj : ∀ z : E, ∃ a b, z = eval₂Hom φ y a / eval₂Hom φ y b)
    (Q : Ideal (MvPolynomial (Fin n) k)) (hQF : IsField (GenSec k e Q))
    (hQK : RingHom.ker ((Ideal.Quotient.mk
        (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
          (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q) :
    IsField (SecAlg (Q.map (MvPolynomial.map φ)) y) ∧
      RingHom.ker ((Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map φ)) y)).comp
        (MvPolynomial.map φ)) = Q := by
  let _ : Algebra (MvPolynomial (Par e n) k) E := (eval₂Hom φ y).toAlgebra
  have : FaithfulSMul (MvPolynomial (Par e n) k) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsFractionRing (MvPolynomial (Par e n) k) E := IsFractionRing.of_field _ _ hsurj
  let σ : GenParField k e n ≃ₐ[MvPolynomial (Par e n) k] E := FractionRing.algEquiv _ E
  have hσX : ∀ p, σ (genPar k e n p) = y p := fun p => by
    show σ (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)) = y p
    exact (σ.commutes (X p)).trans (eval₂_X _ _ p)
  have hσC : (σ : GenParField k e n →+* E).comp (algebraMap k (GenParField k e n)) = φ := by
    refine RingHom.ext fun c => ?_
    show σ (algebraMap k (GenParField k e n) c) = φ c
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n), σ.commutes]
    exact eval₂_C _ _ _
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p
  let QF := Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))
  let QE := Q.map (MvPolynomial.map φ)
  let M : MvPolynomial (Fin n) (GenParField k e n) ≃+* MvPolynomial (Fin n) E :=
    MvPolynomial.mapEquiv (Fin n) σ.toRingEquiv
  have hmσ : (M : MvPolynomial (Fin n) (GenParField k e n) →+* MvPolynomial (Fin n) E) =
      MvPolynomial.map (σ : GenParField k e n →+* E) :=
    RingHom.ext fun _ => rfl
  have hIJ : secIdeal QE y = (secIdeal QF (genPar k e n)).map
      (M : MvPolynomial (Fin n) (GenParField k e n) →+* MvPolynomial (Fin n) E) := by
    rw [hmσ]
    simp only [secIdeal, Ideal.map_sup, Ideal.map_span, QF, QE, Ideal.map_map, hmm, hσC]
    congr 3
    · rw [← Set.range_comp]
      congr 1
      funext i
      simp [secForm, linForm, hσX]
    · rw [Set.image_singleton]
      congr 1
      simp [chartForm, linForm, hσX]
  let τ : GenSec k e Q ≃+* SecAlg QE y := Ideal.quotientEquiv _ _ M hIJ
  refine ⟨MulEquiv.isField hQF τ.symm.toMulEquiv, ?_⟩
  have hc : (Ideal.Quotient.mk (secIdeal QE y)).comp (MvPolynomial.map φ) =
      (τ : GenSec k e Q →+* SecAlg QE y).comp
        ((Ideal.Quotient.mk (secIdeal QF (genPar k e n))).comp
          (MvPolynomial.map (algebraMap k (GenParField k e n)))) := by
    refine RingHom.ext fun p => ?_
    show Ideal.Quotient.mk (secIdeal QE y) (MvPolynomial.map φ p) =
      Ideal.Quotient.mk (secIdeal QE y) (MvPolynomial.map (σ : GenParField k e n →+* E)
        (MvPolynomial.map (algebraMap k (GenParField k e n)) p))
    rw [MvPolynomial.map_map, hσC]
  rw [hc, RingHom.ker_comp_of_injective _ (f := (τ : GenSec k e Q →+* SecAlg QE y)) τ.injective]
  exact hQK

theorem residue_algebraMap {K : Type*} [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (a : MvPolynomial (Par e n) (𝓞 K)) :
    algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) a) =
      eval₂Hom (resToKappa e n v) (parYκ e n v) (a.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)) := by
  have h : (algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) =
      (eval₂Hom (resToKappa e n v) (parYκ e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) v.asIdeal.ResidueField)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C, eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact (Ideal.ResidueField.map_algebraMap v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
        (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm c).symm
    · simp only [RingHom.comp_apply, MvPolynomial.map_X, eval₂Hom_X']
      rfl
  exact RingHom.congr_fun h a

theorem residue_surj {K : Type*} [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (z : (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField) :
    ∃ a b, z = eval₂Hom (resToKappa e n v) (parYκ e n v) a / eval₂Hom (resToKappa e n v) (parYκ e n v) b := by
  obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal (ParDVR e n v)) z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl r
  refine ⟨a.map (algebraMap (𝓞 K) v.asIdeal.ResidueField),
    (s : MvPolynomial (Par e n) (𝓞 K)).map (algebraMap (𝓞 K) v.asIdeal.ResidueField), ?_⟩
  have hs : algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField
      (algebraMap _ (ParDVR e n v) (s : MvPolynomial (Par e n) (𝓞 K))) ≠ 0 :=
    ((IsLocalization.map_units (ParDVR e n v) s).map _).ne_zero
  rw [← residue_algebraMap, ← residue_algebraMap, eq_div_iff hs, ← map_mul, IsLocalization.mk'_spec]

end SecIdealOfPrime

theorem SecIdealOfPrime.proof (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) (hField : SecAlgField.Statement) (hKer : GenSecKer.Statement) :
    SecIdealOfPrime.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨hQ, hQdim⟩ := hDim K n e I f v hI hf W hW
  obtain ⟨g, hg⟩ := hExist v.asIdeal.ResidueField n (e + 1) (reduceMod v W) hQ hQdim

  have hψ : Function.Injective (eval₂Hom (resToKappa e n v) (parYκ e n v)) := fun _ _ hpq =>
    hInd K e n v hpq
  obtain ⟨hFieldE, hkerE⟩ := SecIdealOfPrime.secAlg_of_ratFunc n e (resToKappa e n v) (parYκ e n v) hψ
    (SecIdealOfPrime.residue_surj e n v) (reduceMod v W) (hField _ n e _ g hQ hg) (hKer _ n e _ g hQ hg)

  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let QE := (reduceMod v W).map (MvPolynomial.map (resToKappa e n v))
  let T := secIdeal QE (parYκ e n v)
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p
  let ι : 𝓞 K →+* R := algebraMap (𝓞 K) R
  let ρ : R →+* E := algebraMap R E
  have hρ : Function.Surjective ρ := Ideal.algebraMap_residueField_surjective _
  let Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E := MvPolynomial.map ρ
  have hΨ : Function.Surjective Ψ := MvPolynomial.map_surjective _ hρ
  have hcomp : ρ.comp ι = (resToKappa e n v).comp (algebraMap (𝓞 K) k) := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
        (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm a).symm
  have hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := hW.1.1.2
  let WR : Ideal (MvPolynomial (Fin n) R) := W.map (MvPolynomial.map ι)
  let S := secIdeal (modelR e I v) (parY e n v)
  have hWR : WR.map Ψ = QE := by
    simp only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]
    rfl
  have hM : (modelR e I v).map Ψ ≤ QE := by
    rw [← hWR]
    exact Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))
  have hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ =
      Ideal.span (Set.range (secForm (parYκ e n v))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [Ψ, secForm, linForm, parYκ, ρ]
    rfl
  have hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ =
      Ideal.span {chartForm (parYκ e n v) - 1} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Ψ, chartForm, linForm, parYκ, ρ]
    rfl
  have hT : (S ⊔ WR).map Ψ = T := by
    simp only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hkerΨ : RingHom.ker Ψ ≤ WR := by
    have h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C :=
      IsScalarTower.algebraMap_eq _ _ _
    have hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι := by
      rw [h1, ← Ideal.map_map]
      exact Localization.AtPrime.map_eq_maximalIdeal.symm
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map,
      ← MvPolynomial.map_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono (le_sup_right.trans hJW)
  let Φ : MvPolynomial (Fin n) R →+* SecAlg QE (parYκ e n v) := (Ideal.Quotient.mk T).comp Ψ
  have hker : RingHom.ker Φ = S ⊔ WR := by
    have : RingHom.ker Φ = T.comap Ψ := by
      ext x
      simp [Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hkerΨ.trans le_sup_right)

  have hkerPrime : (RingHom.ker Φ).IsPrime := by
    let _ := hFieldE.toField
    exact RingHom.ker_isPrime Φ
  have hSle : S ≤ RingHom.ker Φ := hker ▸ le_sup_left
  have hsec : secIdealOf e I v W = (RingHom.ker Φ).map (Ideal.Quotient.mk S) := by
    rw [hker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
    rfl
  have hcomap : (secIdealOf e I v W).comap (Ideal.Quotient.mk S) = RingHom.ker Φ := by
    rw [hsec, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hSle
  refine ⟨?_, ?_⟩
  · rw [hsec]
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hSle)
  ·
    have hto : toSecB e I v = (Ideal.Quotient.mk S).comp (MvPolynomial.map ι) := rfl
    have hπ : Function.Surjective (MvPolynomial.map (algebraMap (𝓞 K) k) :
        MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k) :=
      MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal)
    rw [hto, ← Ideal.comap_comap, hcomap]
    ext p
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hΦp : Φ (MvPolynomial.map ι p) =
        ((Ideal.Quotient.mk T).comp (MvPolynomial.map (resToKappa e n v)))
          (MvPolynomial.map (algebraMap (𝓞 K) k) p) := by
      simp only [Φ, Ψ, RingHom.comp_apply, MvPolynomial.map_map, hcomp]
    rw [hΦp, ← RingHom.mem_ker, hkerE]
    change MvPolynomial.map (algebraMap (𝓞 K) k) p ∈ W.map (MvPolynomial.map (algebraMap (𝓞 K) k)) ↔ p ∈ W
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot,
      MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField,
      sup_eq_left.mpr (le_sup_right.trans hJW)]

end

end GroundTheory.Heights₂.Heights.Vertical
