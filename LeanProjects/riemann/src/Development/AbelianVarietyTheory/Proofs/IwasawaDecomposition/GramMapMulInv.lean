import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceVec

open GlobalTheory.AdelicLatMove

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_eq (x : WO S T) : frMapAdj S T βS βT x =
    ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * ((x.map (toEAf D)).map (cF D))ᵀ * (T.gram.map (eToEAf D) * βT.val) := by
  have e : ((x.map (cA D))ᵀ).map (toEAf D) = ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => toEAf_cA _
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, e]
  simp only [Matrix.mul_assoc]
  rfl

theorem frMapAdj_add (x y : WO S T) : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  have e : (((x + y).map (toEAf D)).map (cF D))ᵀ = ((x.map (toEAf D)).map (cF D))ᵀ + ((y.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => ((cF D).comp (toEAf D)).map_add (x j i) (y j i)
  rw [frMapAdj_eq, frMapAdj_eq, frMapAdj_eq, e, Matrix.mul_add, Matrix.add_mul]

theorem cF_cF_toEAf (a : AE D) : cF D (cF D (toEAf D a)) = toEAf D a := by
  rw [← toEAf_cA, ← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]

theorem sandwich_cancel {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (hA : A * A' = 1) (hG : G * G' = 1)
    (hB : B * B' = 1) (hH : H * H' = 1) : (G * A) * ((A' * G') * N * (H * B)) * (B' * H') = N := by
  calc _ = (G * (A * A') * G') * N * (H * (B * B') * H') := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hA, hB, Matrix.mul_one, Matrix.mul_one, hG, hH, Matrix.one_mul, Matrix.mul_one]

theorem gram_map_mul_inv : S.gram.map (eToEAf D) * (S.gram⁻¹).map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem frMapAdj_up : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • frMapAdj S T βS βT x) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) (T.gram.map (eToEAf D) * βT.val)
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [frMapAdj_eq]
  exact h _ fun i j => cF_mem_int (hx j i)

theorem frMapAdj_down :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (frMapAdj S T βS βT x) → IsIntM (k • x.map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int (S.gram.map (eToEAf D) * βS.val) ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))
  refine ⟨k, hk, fun x hx i j => ?_⟩
  have h1 := h _ hx
  rw [frMapAdj_eq, sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (gram_map_mul_inv S) βT.mul_inv
    (gram_map_mul_inv T)] at h1
  have h2 : cF D (k • cF D (toEAf D (x i j))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := cF_mem_int (h1 j i)
  rw [nsmul_eq_mul, RingHom.map_mul, map_natCast, cF_cF_toEAf, ← nsmul_eq_mul] at h2
  exact h2

theorem thPVecExists : ∀ D : D7, ThPVecExists D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf₀
  classical
  have hinf := infPart_cA (idemSum_infPart he)
  obtain ⟨f, hf⟩ := exists_isThetaAt hf₀.1 hS hT (a := cA D e) (by rw [← RingHom.map_mul, idemSum_mul_self he]) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf₀.1 S T ΛS ΛT hS hT _ e he f₀ hf₀.2.theta hf₀.2.lat).2
    (isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (frMapAdj_add S T βS βT) (frMapAdj_up S T βS βT)
      (frMapAdj_down S T βS βT) (Pg ∪ Q) (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
  exact ⟨f, hf₀, e, he, hf⟩

end GlobalTheory.PlaceVec

end
