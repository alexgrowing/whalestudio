import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def dualCoord (E : KMod n) :
    (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ E.V i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  invFun v := ∑ i, v i • innerSL ℂ (stdOrthonormalBasis ℂ E.V i)
  left_inv ξ := by
    ext x
    have hx := (stdOrthonormalBasis ℂ E.V).sum_repr' x
    conv_rhs => rw [← hx]
    simp [map_sum, mul_comm]
  right_inv v := by
    ext j
    have ho := (stdOrthonormalBasis ℂ E.V).orthonormal
    simp [orthonormal_iff_ite.mp ho]

theorem norm_dualCoord (E : KMod n) (ξ : E.V →L[ℂ] ℂ) : ‖dualCoord E ξ‖ = ‖ξ‖ := by
  set r := (InnerProductSpace.toDual ℂ E.V).symm ξ with hr
  have h1 : ‖r‖ = ‖ξ‖ := (InnerProductSpace.toDual ℂ E.V).symm.norm_map ξ
  have h2 : ‖(stdOrthonormalBasis ℂ E.V).repr r‖ = ‖r‖ :=
    (stdOrthonormalBasis ℂ E.V).repr.norm_map r
  rw [← h1, ← h2, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (dualCoord E ξ) i = ξ (stdOrthonormalBasis ℂ E.V i) := rfl
  rw [h3, OrthonormalBasis.repr_apply_apply, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ), ← hr,
    norm_inner_symm]

def dualAct (E : KMod n) : (E.V →L[ℂ] E.V) →ₗ[ℂ]
    (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) where
  toFun T := LinearMap.toContinuousLinearMap
    ((dualCoord E).toLinearMap ∘ₗ
      (((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip T : (E.V →L[ℂ] ℂ) →L[ℂ] (E.V →L[ℂ] ℂ)) :
        (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ∘ₗ (dualCoord E).symm.toLinearMap)
  map_add' S T := by
    ext v : 1
    simp
  map_smul' c T := by
    ext v : 1
    simp

theorem dualAct_apply (E : KMod n) (T : E.V →L[ℂ] E.V) (v) :
    dualAct E T v = dualCoord E ((dualCoord E).symm v ∘L T) := by
  simp [dualAct]

theorem continuous_unitary_inv :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k⁻¹ := by
  refine Continuous.subtype_mk (p := (· ∈ Matrix.unitaryGroup (Fin n) ℂ)) ?_ _
  simpa using (continuous_subtype_val.star :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => star k.1)

theorem dualRep_exists {n : ℕ} (E : KMod n) :
    ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))
      (ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
        (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))),
      Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  have hact : ∀ k ξ, dualAct E (E.ρ k⁻¹) (dualCoord E ξ) = dualCoord E (ξ ∘L E.ρ k⁻¹) := by
    intro k ξ
    rw [dualAct_apply, LinearEquiv.symm_apply_apply]
  let ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
      (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => dualAct E (E.ρ k⁻¹)
      map_one' := by
        ext1 v
        rw [dualAct_apply, inv_one, map_one]
        change dualCoord E ((dualCoord E).symm v ∘L ContinuousLinearMap.id ℂ E.V) = v
        rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro k l
        ext1 v
        obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
        rw [ContinuousLinearMap.mul_apply, hact l, hact k, hact (k * l), _root_.mul_inv_rev, map_mul]
        rfl }
  refine ⟨dualCoord E, ρ', ?_, ?_, fun k ξ => (hact k ξ).symm⟩
  · have h1 : Continuous (dualAct E) := LinearMap.continuous_of_finiteDimensional _
    exact h1.comp (E.cont.comp continuous_unitary_inv)
  · intro k v
    obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
    have hle : ∀ (l : Matrix.unitaryGroup (Fin n) ℂ) (η : E.V →L[ℂ] ℂ), ‖η ∘L E.ρ l‖ ≤ ‖η‖ := by
      intro l η
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      simpa [E.iso] using η.le_opNorm (E.ρ l x)
    have hback : (ξ ∘L E.ρ k⁻¹) ∘L E.ρ k = ξ := by
      ext x
      have : E.ρ k⁻¹ (E.ρ k x) = x := by
        have h := congrArg (fun T : E.V →L[ℂ] E.V => T x) (E.ρ.map_mul k⁻¹ k)
        simpa using h.symm
      simp [this]
    have h2 : ‖ξ ∘L E.ρ k⁻¹‖ = ‖ξ‖ := by
      refine le_antisymm (hle _ _) ?_
      calc ‖ξ‖ = ‖(ξ ∘L E.ρ k⁻¹) ∘L E.ρ k‖ := by rw [hback]
        _ ≤ _ := hle _ _
    change ‖dualAct E (E.ρ k⁻¹) (dualCoord E ξ)‖ = _
    rw [hact, norm_dualCoord, norm_dualCoord, h2]

end GlobalTheory.CompanionTheory.RealCount
