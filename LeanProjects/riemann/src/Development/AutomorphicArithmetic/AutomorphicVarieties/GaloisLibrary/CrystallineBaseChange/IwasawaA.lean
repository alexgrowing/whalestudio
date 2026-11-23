import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import GroundTheory.AutomorphicForms.ReductionIwasawa

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GroundTheory.Automorphic
open scoped Matrix

private theorem upper_eq {R : Type} [CommRing R] (b : GL (Fin 2) R) (h : b 1 0 = 0) (h0 : IsUnit (b 0 0)) (h1 : IsUnit (b 1 1)) :
    ∃ (z y : Rˣ) (x : R), b = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y x := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, d⁻¹ * a, (d⁻¹ : Rˣ) * b 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, h, ← ha, ← hd]

private theorem orth {E : Type} [NormedField E] (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin 2) (Fin 2) E)
    (hk : ∀ y : Fin 2 → E, Reduction.euclidNorm (y ᵥ* k) = Reduction.euclidNorm y) (i j : Fin 2) :
    φ (k i 0) * φ (k j 0) + φ (k i 1) * φ (k j 1) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have h : ∀ s t : E, (φ s * φ (k 0 0) + φ t * φ (k 1 0)) ^ 2 + (φ s * φ (k 0 1) + φ t * φ (k 1 1)) ^ 2 = φ s ^ 2 + φ t ^ 2 := by
    intro s t
    have := hk ![s, t]
    unfold Reduction.euclidNorm at this
    rw [Real.sqrt_inj (by positivity) (by positivity)] at this
    simpa [← hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using this
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [map_one, map_zero] at h1 h2 h3
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith

theorem UpperTheory.V.Br.iwasawaA :
    UpperTheory.V.Br.IwasawaA := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨z, y, x, hz⟩ := upper_eq b (hb (show (0 : Fin 2) < 1 by decide))
    (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0) (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1)
  have hr : ((Matrix.GeneralLinearGroup.map (TR.pInf F) k : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) ∈
      Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j w
    have := orth (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
        (map_zero _) x) _ (hk.1 w) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Eq.trans this ?_
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hu : Matrix.GeneralLinearGroup.map (pFin F) k ∈ AdelicGLn.integralFiniteGL F 2 :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall F 2).2 hk.2
  obtain ⟨hu1, hu2⟩ := (AdelicGLn.mem_integralFiniteGL_iff F 2).1 hu
  refine ⟨z, y, x, ⟨_, hr⟩, Matrix.GeneralLinearGroup.map (pFin F) k, ?_, ?_⟩
  · refine mem_KLev.2 ⟨fun a c => mem_Ohat.2 (hu1 a c), fun a c => mem_Ohat.2 (hu2 a c), fun a c => ⟨_, ?_, by rw [Nat.cast_one, one_mul]⟩⟩
    refine sub_mem (mem_Ohat.2 (hu1 a c)) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · have e : Unitary.toUnits (⟨_, hr⟩ : TR.Kinf F 2) = Matrix.GeneralLinearGroup.map (TR.pInf F) k := Units.ext rfl
    rw [e, TR.infGL_mul_finGL, ← hz]
