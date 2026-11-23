import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem approximationAdelic_holds : ApproxA := by
  intro F E _ _ _ _ _ D hD u
  obtain ⟨d, hd, hdu⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) u
  obtain ⟨b0, t, ht, heq⟩ :=
    Formalism.UG.P.csGlob_approx Formalism.UG.P.integral_adele_approximation_holds (d * D) (mul_ne_zero hd hD) _ hdu
  rw [Formalism.L2.DIV.levelafC_eq_incl, Formalism.L2.DIV.levelafC_eq_incl] at heq
  have hdE : algebraMap (𝓞 F) E d ≠ 0 := by
    intro h0
    apply hd
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) E) (by rw [h0, map_zero])
  have hinv : iA F E (algebraMap (𝓞 F) E d)⁻¹ * iA F E (algebraMap (𝓞 F) E d) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hdE, map_one]
  refine ⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b0, t, ht, ?_⟩
  calc u = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 F) E d) * u) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 E) E b0) +
          iA F E (algebraMap (𝓞 F) E d) * iA F E (algebraMap (𝓞 F) E D) * t) := by
        rw [heq, map_mul (algebraMap (𝓞 F) E) d D, map_mul (iA F E)]
    _ = _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul, map_mul]

theorem unitNearOne_holds : UnitNear := by
  intro F E _ _ _ _ _ _ hc v π hπ n s hs
  classical
  set S := Formalism.L2.Herm.intAf F E with hS
  let st : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨s i j, hs i j⟩
  let et : S := Formalism.L2.DIV.adS F E (Formalism.L2.DIV.idemAd (fun w => w = v))
  let pt : S := Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)
  let Mt : Matrix (Fin n) (Fin n) S := et • (1 - pt • st) + (1 - et) • (1 : Matrix (Fin n) (Fin n) S)
  have hMt : IsUnit Mt := by
    refine Formalism.L2.DIV.isUnit_matrix_of_resS hc Mt fun PP => ?_
    have h1 : Mt.map (Formalism.L2.DIV.resS F PP) = 1 := by
      by_cases hw : Formalism.L2.DIV.underPl F PP = v
      · have he : Formalism.L2.DIV.resS F PP et = 1 :=
          Formalism.L2.DIV.resS_idemAd_pos PP (Formalism.L2.DIV.underPl F PP) rfl hw
        have hp : Formalism.L2.DIV.resS F PP pt = 0 := by
          show Formalism.L2.DIV.resS F PP (Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)) = 0
          rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
          have : π ∈ (Formalism.L2.DIV.underPl F PP).asIdeal := by rw [hw]; exact hπ
          exact this
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hp, hij]
      · have he : Formalism.L2.DIV.resS F PP et = 0 :=
          Formalism.L2.DIV.resS_idemAd_neg PP (Formalism.L2.DIV.underPl F PP) rfl hw
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hij]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hMt
  set e := eAt E v with he_def
  have hee : e * e = e := by
    rw [he_def, show eAt E v = eP E (fun w => w = v) from rfl, (idempotentCalculation_holds F E).2.1]
    exact eP_congr (fun u => and_self_iff)
  have het : ((et : S) : E ⊗[F] Formalism.L2.Herm.Af F) = e := rfl
  have hpt : ((pt : S) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 F) E π) := by
    show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  let φ := (S.subtype).mapMatrix (m := Fin n)
  refine ⟨((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S).map S.subtype,
    fun i j => (((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) i j).2, ?_⟩
  have hMR : Mt * ((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) = 1 := by
    rw [← hU]; exact U.mul_inv
  have hφ : φ Mt = glueM e (1 - iA F E (algebraMap (𝓞 F) E π) • s) := by
    ext i j
    by_cases hij : i = j <;>
      simp [φ, Mt, glueM, st, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        het, hpt, hij]
  have h2 := congrArg φ hMR
  rw [map_mul, map_one, hφ] at h2
  rw [← glue_smul_same hee]
  exact congrArg (fun M => e • M) h2

theorem integralAtInverse_holds : IntAtInv := by
  intro F E _ _ _ _ _ _ hc n v y hy hI
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hy' : Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) := hy
  rw [hJ, Matrix.mul_one] at hy'
  have hinv : (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    Units.inv_eq_of_mul_eq_one_left hy'
  have hσ : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  intro i j
  rw [hinv]
  show eAt E v * Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)
    (((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) j i) ∈ _
  have hm := (Formalism.L2.DIV.sigS hc ⟨_, hI j i⟩).2
  rw [Formalism.L2.DIV.sigS_coe, map_mul, hσ] at hm
  exact hm

end Formalism.L2.GenusGluing.Gen
