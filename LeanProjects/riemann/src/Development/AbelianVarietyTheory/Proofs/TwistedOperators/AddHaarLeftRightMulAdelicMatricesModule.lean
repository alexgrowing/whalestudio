import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrictStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongrStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReducedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIntegersTopologyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetMatrixPairIntegralOutsideStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingPairOfTuplesToTupleOfPairsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTensStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNormStatement

noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped NNReal ENNReal TensorProduct

theorem chi_Af (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (Af F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = ∏ᶠ v, ‖evalV F v M.det‖ := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_matrixPair_integral_outside F κ M M⁻¹
  obtain ⟨hOc, hOs, hOt⟩ := GlobalTheory.T.finiteIntegers_topology F S
  let _ : MeasurableSpace (OPart F S) := borel _
  have _ : BorelSpace (OPart F S) := ⟨rfl⟩

  let φS : Af F →+* SPart F S := RingHom.pi fun v => (evalV F v.1).toRingHom
  let φO : Af F →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (evalV F v.1).toRingHom
  let ι : OPart F S →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (v.1.adicCompletionIntegers F).toSubring.subtype.comp (Pi.evalRingHom _ v)
  have hι : Function.Injective ι := fun x y h => funext fun v => Subtype.ext (congrFun h v)
  let MS : Matrix κ κ (SPart F S) := φS.mapMatrix M
  let MO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M i j), (hS v.1 v.2 i j).1⟩
  let NO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M⁻¹ i j), (hS v.1 v.2 i j).2⟩
  have hdS : MS.det = φS M.det := (RingHom.map_det φS M).symm
  have huS : IsUnit MS.det := hdS ▸ hM.map φS
  have hMO : ι MO.det = φO M.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hNO : ι NO.det = φO M⁻¹.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hON : MO.det * NO.det = 1 := hι (by
    rw [map_mul, hMO, hNO, ← map_mul, ← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one,
      map_one, map_one])
  have huO : IsUnit MO.det := ⟨⟨_, _, hON, by rw [mul_comm]; exact hON⟩, rfl⟩
  let j : ((κ → SPart F S) × (κ → OPart F S)) →+ (κ → Af F) :=
    ((jS F S).toAddMonoidHom.compLeft κ).comp (zipHom κ (SPart F S) (OPart F S))
  have hj : IsOpenEmbedding j :=
    (IsOpenEmbedding.piMap fun _ => GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart F S).comp (GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (SPart F S) (OPart F S))
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → Af F) ((κ → SPart F S) × (κ → OPart F S)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE MS huS) (mulVecCE MO huO)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      apply RestrictedProduct.ext
      intro v
      change evalV F v ((M *ᵥ j x) i) = evalV F v (jS F S ((MS *ᵥ x.1) i, (MO *ᵥ x.2) i))
      rw [evalV_jS]
      by_cases hv : v ∈ S
      · rw [dif_pos hv]
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dif_pos hv]
        rfl
      · rw [dif_neg hv]
        change _ = ι ((MO *ᵥ x.2) i) ⟨v, hv⟩
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dif_neg hv]
        rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, addEquivAddHaarChar_eq_one_of_compactSpace (mulVecCE MO huO), mul_one,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (SPart F S)
      (by show IsArtinianRing (∀ v : S, Fv F v.1); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ huS,
    GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm F S _ huS, hdS,
    finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 := GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers F v (MO.det ⟨v, hvS⟩) (NO.det ⟨v, hvS⟩) (congrFun hON ⟨v, hvS⟩)
    have h2 : (MO.det ⟨v, hvS⟩ : Fv F v) = evalV F v M.det := congrFun hMO ⟨v, hvS⟩
    show ‖evalV F v M.det‖ = 1
    rw [← h2]
    exact h1

theorem chi_AF (F : Type) [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (∏ w, ‖(fstA F M.det) w‖) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  have hd₁ : (M.map (fstA F)).det = fstA F M.det := (RingHom.map_det (fstA F).toRingHom M).symm
  have hd₂ : (M.map (sndA F)).det = sndA F M.det := (RingHom.map_det (sndA F).toRingHom M).symm
  have hu₁ : IsUnit (M.map (fstA F)).det := hd₁ ▸ hM.map (fstA F)
  have hu₂ : IsUnit (M.map (sndA F)).det := hd₂ ▸ hM.map (sndA F)
  let j : ((κ → Ainf F) × (κ → Af F)) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → AF F) ((κ → Ainf F) × (κ → Af F)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE (M.map (fstA F)) hu₁) (mulVecCE (M.map (sndA F)) hu₂)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      refine Prod.ext ?_ ?_
      · change fstA F _ = _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl
      · change sndA F _ = _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, chi_Af F _ hu₂, hd₂,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F)
      (by show IsArtinianRing (∀ v : InfinitePlace F, v.Completion); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ hu₁, hd₁,
    GlobalTheory.GaugeProdFormula.modu_infinite F _ (hM.map (fstA F))]

theorem chi_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    addEquivAddHaarChar (lrCE g a) = GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) ^ n *
      GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) ^ m := by
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor F E m n g a
  apply NNReal.coe_injective
  rw [hchar, chi_AF F Λ hΛ, hdet, GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm F E]
  simp [map_mul, map_pow]

theorem smul_map_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (μ : Measure (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) [μ.IsAddHaarMeasure]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    μ = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) ^ n *
      (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) : ℝ≥0∞) ^ m) • μ.map (lrCE g a) := by
  have h := addEquivAddHaarChar_smul_map μ (lrCE g a)
  rw [chi_lr F E m n g a] at h
  calc μ = _ := h.symm
    _ = _ := by rw [ENNReal.smul_def]; push_cast; rfl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem modu_lrMul : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  intro D m n μ hμ g a
  have _ : LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have _ : SecondCountableTopology (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have hb : BorelSpace (Fin m → Fin n → AE D) := inferInstance
  have _ : BorelSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    ⟨by first | rfl | exact hb.measurable_eq⟩
  exact smul_map_lr D.host.F D.host.E m n μ g a

end GlobalTheory.ModuLR
