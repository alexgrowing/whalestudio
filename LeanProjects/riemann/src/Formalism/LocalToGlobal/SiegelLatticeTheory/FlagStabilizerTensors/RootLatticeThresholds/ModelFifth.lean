import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFourth

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.flagStabilizerModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel Formalism.L2.SG.unitMultiplierModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem mp_model {k0 : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp Wq) {δ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r}
    (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, ‖d (W q.1.1)‖ = ‖d (W q.1.2)‖)
    (hZ : Zhat (k0 + 1) r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP W d) (μ : Measure (Mt (k0 + 1) r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords (k0 + 1) r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) =
      c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ W := by
  have hzS : Formalism.FourierDecayAlt.C2.StdZ (k0 + 1) r Ds.z := ⟨Ds.z_mem, Ds.T_pos⟩
  have hz'S : Formalism.FourierDecayAlt.C2.StdZ (k0 + 1) r Ds.z' := ⟨Ds.z'_mem, Ds.T'_pos⟩
  have hG := good_of Ds hδ hd hZ
  have hu : IsUnit δ.det := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 δ hδ).1
  have hδi : δ⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 δ hδ).2
  obtain ⟨Ds', hD1, hD2⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r (by omega) Ds.z' Ds.z hz'S hzS
  set d' : Fin (r + 1) → ℂ := fun a => star (d (W a)) with hd'def
  have hd' : ∀ a, d' a ≠ 0 := fun a => star_ne_zero.2 (hd _)
  have hZ' : Zhat (k0 + 1) r Ds'.z Ds'.z' δ⁻¹ = Formalism.FourierDecayAlt.C2.monoP W d' := by
    ext i a
    rw [hD1, hD2, Formalism.L2.SG.Pf.RootHaarLoc.zhat_inv Ds.z Ds.z' hδ hu i a, hZ]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, hd'def]
    by_cases hai : a = W i
    · have hia : i = W a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      all_goals (try (rw [hai, wPt_invol]))
    · have hia : ¬ i = W a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, star_zero]
  have hG' := good_of Ds' hδi hd' hZ'

  set φ : Mt (k0 + 1) r → Formalism.FourierDecayAlt.C2.Lstidx W → ℂ := phi0 Ds W with hφ
  set φ' : Mt (k0 + 1) r → Formalism.FourierDecayAlt.C2.Lstidx W → ℂ :=
    fun x => phi0 Ds' W (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ)) with hφ'
  have hφc : Continuous φ := continuous_radial_phi Ds
  have hφ'c : Continuous φ' := by
    refine (continuous_radial_phi Ds').comp ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

  have hRinv : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      δ⁻¹ * Matrix.of x * δ ∈ Formalism.FourierDecayAlt.C6.Rset δ⁻¹ := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    have : δ * (δ⁻¹ * Matrix.of x * δ) * δ⁻¹ = Matrix.of x := by
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [this]
    exact hx.1

  have hroot : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      Formalism.MainNotions.S.rootCoords (k0 + 1) r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ)) = Tmap pN (φ' x) := by
    intro x hx
    have hm := hRinv x hx
    have e2 := u_eq_low Ds' hδi hd' hG' hm
    have hρ := rhoF_unique Ds' hδi hd' hG' (φ' x) hm (by
      rw [← Matrix.conjTranspose_conjTranspose (Formalism.FourierDecayAlt.C2.uMap _ _ _ _), e2])
    have h1 := Formalism.L2.SG.Pf.RootHaarLoc.rootCoords_psiG Ds'.z Ds' rfl pN hδi hd' hZ' (Tmap pN (φ' x))
    rw [Tinv_Tmap, ← hρ, hD1] at h1
    exact h1

  have hkey : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      φ x = Formalism.L2.SG.lowerTriangularModel.linv W (Rm pN d (φ' x)) := by
    intro x hx
    have hm := hRinv x hx
    have e1 := u_eq_low Ds hδ hd hG hx
    have e2 := u_eq_low Ds' hδi hd' hG' hm
    have zh := Formalism.L2.SG.HermitianMatrixIdentities.zhat_uMap hzS hz'S hδ hx.1 hx.2
    have hinv : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x)⁻¹ = (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x))⁻¹ := by
      have hxu : IsUnit (Matrix.of x).det := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 _ hx.1.1).1
      have hm1 := uMap_mul Ds hx.1 (PI.WBL.Cv.n_inv hx.1)
      rw [Matrix.mul_nonsing_inv _ hxu, uMap_one _ hzS] at hm1
      exact (Matrix.inv_eq_right_inv hm1.symm).symm
    have e1' : (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x))ᴴ = low W (φ x) := e1
    have e2' : (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds'.z (δ⁻¹ * Matrix.of x * δ))ᴴ = low W (φ' x) := e2
    have hU : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x) = (low W (φ x))ᴴ := by
      rw [← e1', Matrix.conjTranspose_conjTranspose]
    have hU' : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z' (δ⁻¹ * Matrix.of x * δ) = (low W (φ' x))ᴴ := by
      rw [← hD1, ← e2', Matrix.conjTranspose_conjTranspose]
    rw [hU', hinv, hU, hZ, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose] at zh

    have h1 : low W (Rm pN d (φ' x)) * Formalism.FourierDecayAlt.C2.monoP W d = (low W (φ x))⁻¹ * Formalism.FourierDecayAlt.C2.monoP W d := by
      rw [low_R_mono pN d hd, zh]
    have h2 : low W (Rm pN d (φ' x)) = (low W (φ x))⁻¹ := by
      have := congrArg (· * Formalism.FourierDecayAlt.C2.monoP (wPt pN).symm (fun j => (d ((wPt pN).symm j))⁻¹)) h1
      simp only [Matrix.mul_assoc, mono_mul_inv pN d hd, Matrix.mul_one] at this
      exact this
    have hlu : IsUnit (low W (φ x)).det := Formalism.L2.SG.lowerTriangularModel.isUnit_low W _
    have h3 : low W (φ x) = (low W (Rm pN d (φ' x)))⁻¹ := by
      rw [h2, Matrix.nonsing_inv_nonsing_inv _ hlu]
    funext q
    rw [← low_coord W (φ x) q, h3]
    rfl

  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ := ae_iff.2 hconc
  have hB : μ.map φ' = c • volume := by
    have hA : μ.map (Tmap pN ∘ φ') = c • volume := by
      rw [← hmap]
      refine Measure.map_congr ?_
      filter_upwards [hae] with x hx
      exact (hroot x hx).symm
    have hTm : Measurable (Tmap pN) := (Tmap_mp pN).measurable
    have e : φ' = Tinv pN ∘ (Tmap pN ∘ φ') := by
      funext x; simp [Tinv_Tmap]
    rw [e, ← Measure.map_map (Tinv_mp pN).measurable (hTm.comp hφ'c.measurable), hA, Measure.map_smul,
      (Tinv_mp pN).map_eq]
  have hC : μ.map φ = c • volume := by
    have hlinv := Formalism.L2.SG.lowerTriangularModel.linv_mp W
    have hR := Rm_mp pN d hd hdm
    rw [Measure.map_congr (g := Formalism.L2.SG.lowerTriangularModel.linv W ∘ Rm pN d ∘ φ') (by
      filter_upwards [hae] with x hx
      exact hkey x hx)]
    rw [← Measure.map_map hlinv.measurable (hR.measurable.comp hφ'c.measurable),
      ← Measure.map_map hR.measurable hφ'c.measurable, hB, Measure.map_smul, hR.map_eq, Measure.map_smul,
      hlinv.map_eq]
  have hrho := rhoF_meas Ds hδ hd hG
  have hD : μ = μ.map ((fun y => Matrix.of.symm (rhoF Ds δ W y)) ∘ φ) := by
    conv_lhs => rw [← Measure.map_id (μ := μ)]
    refine Measure.map_congr ?_
    filter_upwards [hae] with x hx
    have hρ := rhoF_unique Ds hδ hd hG (φ x) hx (by
      rw [← Matrix.conjTranspose_conjTranspose (Formalism.FourierDecayAlt.C2.uMap _ _ _ _), u_eq_low Ds hδ hd hG hx]
      rfl)
    show x = Matrix.of.symm (rhoF Ds δ W (φ x))
    rw [← hρ]
    rfl
  rw [hD, ← Measure.map_map hrho hφc.measurable, hC, Measure.map_smul]
  rfl

end Formalism.L2.SG.flagStabilizerModel

end
