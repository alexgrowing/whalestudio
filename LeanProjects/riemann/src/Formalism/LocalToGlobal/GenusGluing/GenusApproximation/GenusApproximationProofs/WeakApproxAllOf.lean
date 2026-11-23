import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section At

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem intAt_congr {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    {Y Y' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : eAt E v • Y = eAt E v • Y') :
    IntAt v Y ↔ IntAt v Y' := by
  have h' : ∀ i j, eAt E v * Y i j = eAt E v * Y' i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  unfold IntAt
  simp only [h']

theorem weakApproxU_at (hSD : ShiftDiag) (hCS : CayleyStep) (hII : IntAtInv) (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ UAd hc n) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ ∈ URat hc n,
      IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  classical
  have he : eAt E v * eAt E v = eAt E v := by
    have h := (idempotentCalculation_holds F E).2.1 (fun w => w = v) (fun w => w = v)
    exact h.trans (eP_congr (fun u => and_self_iff))
  have hσe : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  obtain ⟨t, ht, w, hw⟩ := hSD F E hc v n (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
  have hts : ∀ i, t i * star (t i) = 1 := fun i => by rw [mul_comm]; exact ht i

  let γ0 : GL (Fin n) E :=
    { val := Matrix.diagonal t
      inv := Matrix.diagonal (fun i => star (t i))
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [hts, Matrix.diagonal_one]
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [ht, Matrix.diagonal_one] }
  have hγ0 : γ0 ∈ URat hc n := by
    show Formalism.UG.cT _ (Matrix.diagonal t) * 1 * Matrix.diagonal t = 1
    rw [Matrix.mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have h1 : ∀ i, ((hc.sig : E →ₐ[F] E) : E →+* E) (t i) * t i = 1 := fun i => ht i
    simp only [h1, Matrix.diagonal_one]
  set g0 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := Formalism.UG.bc (iA F E) γ0 with hg0
  have hg0v : (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Matrix.diagonal fun i => iA F E (t i) := by
    rw [hg0]
    show (Matrix.diagonal t).map (iA F E) = _
    exact Matrix.diagonal_map (map_zero _)
  have hg0A : g0 ∈ UAd hc n := (ratIn hc n ⟨γ0, hγ0⟩).2
  rw [← hg0v] at hw

  set x1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := g0⁻¹ * x with hx1
  have hx1A : x1 ∈ UAd hc n := mul_mem (inv_mem hg0A) hx
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hx1U : x1 ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h := hx1A
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
    rwa [hJ] at h
  set x2 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := glueU he x1 with hx2
  have hx2A : x2 ∈ UAd hc n := by
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
    rw [hJ]
    exact glueU_mem _ he hσe hx1U

  set P : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hP
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) with hB
  have h1x : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P := by
    rw [hx1, Units.val_mul, hP, Matrix.mul_add, Units.inv_mul, add_comm]
  have hxB : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B =
      (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [h1x, hB]
    calc ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P *
          (w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))))
        = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P * Matrix.adjugate P) * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
          rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
      _ = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P.det • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
            (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [Matrix.mul_adjugate]
      _ = (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul, smul_smul]
  have heB : eAt E v • (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) =
      eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hxB, smul_smul, mul_comm w, hw]
  have hglue1 : glueM (eAt E v) (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) = 1 := by
    unfold glueM
    rw [heB, ← add_smul, add_sub_cancel, one_smul]
  set c : E ⊗[F] Formalism.L2.Herm.Af F := iA F E (2⁻¹ : E) with hcdef
  have h2c : (2 : E ⊗[F] Formalism.L2.Herm.Af F) * c = 1 := by
    rw [hcdef, ← map_ofNat (iA F E) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  set s : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + 2 * (1 - eAt E v) with hs
  set s' : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + c * (1 - eAt E v) with hs'
  have hss : s * s' = 1 := by
    rw [hs, hs']
    linear_combination (-c) * he + (1 - eAt E v) ^ 2 * h2c
  have h1x2 : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      s • glueM (eAt E v) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
        (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
    rw [hx2, glueU_val, hs]
    ext i j
    simp only [glueM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) * he
  have hright : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
      (s' • glueM (eAt E v) B) = 1 := by
    rw [h1x2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul, glueM_mul he, hglue1]
  have hx2u : IsUnit ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :=
    ⟨⟨_, _, hright, mul_eq_one_comm.mp hright⟩, rfl⟩

  obtain ⟨γ1, hγ1, hI1⟩ := hCS F E hc n v x2 hx2A hx2u
  have hI1' : IntAt v ((x1⁻¹ * Formalism.UG.bc (iA F E) γ1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    refine (intAt_congr v ?_).1 hI1
    rw [Units.val_mul, Units.val_mul]
    exact glue_smul_same he _ _
  have hγ : γ0 * γ1 ∈ URat hc n := mul_mem hγ0 hγ1
  have hprod : x1⁻¹ * Formalism.UG.bc (iA F E) γ1 = x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) := by
    rw [hx1, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hprod] at hI1'
  refine ⟨γ0 * γ1, hγ, ?_, hI1'⟩
  have hyA : x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) ∈ UAd hc n :=
    mul_mem (inv_mem hx) (ratIn hc n ⟨γ0 * γ1, hγ⟩).2
  have hinv : (Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ * x = (x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv]
  rw [hinv]
  exact hII F E hc n v _ hyA hI1'

end At

theorem weakApproxAll_of : ShiftDiag → CayleyStep → IntAtInv → WeakApproxAll := by
  intro hSD hCS hII F E _ _ _ _ _ _ hc n x hx v
  exact weakApproxU_at hSD hCS hII hc n x hx v

end Formalism.L2.GenusGluing.Gen
