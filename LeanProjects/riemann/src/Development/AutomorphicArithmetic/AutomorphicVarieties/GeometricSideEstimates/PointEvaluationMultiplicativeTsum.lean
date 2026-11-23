import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.CmDatumInfinitePlacesComplexSplit
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

private theorem tsum_reindex {α M : Type} [AddCommGroup α] [AddCommMonoid M] [TopologicalSpace M]
    (S T : AddSubgroup α) (e : α ≃ α) (he : ∀ v, v ∈ S ↔ e v ∈ T) (f f' : α → M) (hf : ∀ v, f v = f' (e v)) :
    ∑' v : S, f v.1 = ∑' v : T, f' v.1 := by
  rw [← (e.subtypeEquiv he : S ≃ T).tsum_eq (fun v : T => f' v.1)]
  exact tsum_congr fun v => hf v.1

private def mulEquivRow {R : Type} [CommRing R] {a : ℕ} (γ : GL (Fin a) R) : (Fin a → R) ≃ (Fin a → R) where
  toFun v := v ᵥ* γ.val
  invFun v := v ᵥ* (γ⁻¹).val
  left_inv v := by
    show (v ᵥ* γ.val) ᵥ* (γ⁻¹).val = v
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv v := by
    show (v ᵥ* (γ⁻¹).val) ᵥ* γ.val = v
    rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem ptF_mul (g k : GA E a) (v : Fin a → E) :
    ptF (g * k) v = ptF g v ᵥ* (GeneralLinearGroup.map (pFin E) k).val := by
  show vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (g * k)).val = (vFin v ᵥ* (GeneralLinearGroup.map (pFin E) g).val) ᵥ* _
  rw [map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [IsTotallyComplex E]

private theorem pt_mul (g k : GA E a) (v : Fin a → E) :
    pt (g * k) v = pt g v ᵥ* (GeneralLinearGroup.map (pInf E) k).val := by
  show vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (g * k)).val = (vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val) ᵥ* _
  rw [map_mul, Units.val_mul, Matrix.vecMul_vecMul]

end

theorem UpperTheory.point_evaluation_multiplicative_tsum :
    SumInv := by
  intro E _ _ _ a ha L M _ _ F
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  have h5 := UpperTheory.cmDatum_infinitePlaces_complex_split E a ha
  refine ⟨fun γ t g => ?_, fun g h => ?_, fun U hU hL u hu g => ?_⟩
  · refine tsum_reindex _ _ (mulEquivRow γ) (fun v => ?_) (fun v => F (pt (rt _) v)) (fun v => F (pt (rt g) v))
      (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g (v ᵥ* γ.val) ∈ L
      rw [← (h2 _).2.2, h1, (h3 γ (rt g) v).1, (h2 g).2.2]
    · show F (pt (rt _) v) = F (pt (rt g) (v ᵥ* γ.val))
      rw [h1, (h3 γ (rt g) v).2]
  · refine tsum_reindex _ _ (Equiv.refl _) (fun v => ?_) (fun v => F (pt (rt _) v))
      (fun v => F (sc h.val • (pt (rt g) v ᵥ* h.val))) (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g v ∈ L
      rw [ptF_mul, pFin_infGL, Units.val_one, Matrix.vecMul_one]
    · show F (pt (rt _) v) = F (sc h.val • (pt (rt g) v ᵥ* h.val))
      rw [h5]
  · refine tsum_reindex _ _ (Equiv.refl _) (fun v => ?_) (fun v => F (pt (rt _) v)) (fun v => F (pt (rt g) v))
      (fun v => ?_)
    · show ptF _ v ∈ L ↔ ptF g v ∈ L
      rw [ptF_mul, pFin_finGL]
      refine ⟨fun hv => ?_, hL u hu _⟩
      have h6 := hL u⁻¹ (U.inv_mem hu) _ hv
      rwa [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one] at h6
    · show F (pt (rt _) v) = F (pt (rt g) v)
      rw [h4 U hU u hu, pt_mul, pInf_finGL, Units.val_one, Matrix.vecMul_one]
