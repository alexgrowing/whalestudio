import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.S3

namespace LocalVolumePositivity

variable {P : Type} [Fintype P] {B : MassData P}

theorem unit_level_volume_pos (hP : B.Pos) : 0 < B.unitLevelVolume := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.unitLevelVolume
  exact mul_pos xU0 (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)

theorem pos_μK (hP : B.Pos) : 0 < B.μK := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μK
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.1)

theorem pos_μKpp (hP : B.Pos) : 0 < B.μKpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μKpp
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1)

theorem pos_MM (hP : B.Pos) : 0 < B.MM := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.MM
  exact mul_pos xMo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μS (hP : B.Pos) : 0 < B.μS := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μS
  exact mul_pos xSo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.1)

theorem pos_μS' (hP : B.Pos) : 0 < B.μS' := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μS'
  exact mul_pos xSo' (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp (hP : B.Pos) : 0 < B.μSpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp
  exact mul_pos xSo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp' (hP : B.Pos) : 0 < B.μSpp' := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp'
  exact mul_pos xSo' (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1)

theorem gamma_product_pos (hP : B.Pos) : 0 < B.Gam1 := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.Gam1
  exact prod_pos fun p _ => by unfold MassData.ga; exact div_pos (hp p).2.1 (hp p).2.2.1

theorem pos_tt (hP : B.Pos) : 0 < B.tt := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.tt
  exact prod_pos fun p _ => add_pos one_pos (div_pos (by norm_num) (hp p).1)

theorem pos_idx (hP : B.Pos) : 0 < ∏ p, B.gg p / (B.nn p * B.uk p) := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  exact prod_pos fun p _ => div_pos (hp p).2.2.2.2.1 (mul_pos (hp p).2.2.2.1 (hp p).2.2.1)

end LocalVolumePositivity

open LocalVolumePositivity

theorem middle_level_volume_index : KnatGamma := by
  intro P _ B hP hI p
  obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hP.1 p
  obtain ⟨h1, h2⟩ := hI p
  rw [div_eq_iff qKp.ne'] at h2
  rw [h2, h1]
  unfold MassData.ga
  field_simp

theorem column_identity : Columns := by
  intro P _ B hP hV hL hM hC
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨_, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, hLSpp, hLS', hLSpp'⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ, eN, hLS]; field_simp
  · rw [hdd, ← hG1, hρ]; field_simp
  · unfold MassData.c0; rw [hdd, hLSpp, eN]; field_simp
  · rw [hρ', eN', hLS']; field_simp
  · rw [hdd', ← hG1', hρ']; field_simp
  · unfold MassData.c0'; rw [hdd', hLSpp', eN']; field_simp

theorem local_ratio_product : LocalProduct := by
  intro P _ B hP hO hT hI
  have hP0 := hP
  have hG1 := gamma_product_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hMo : B.Mo = B.μKo ^ 2 / (B.μSo * B.μSo') * B.localVolumeArchimedean := by
    rw [← hO]; field_simp
  have hM : ∏ p, B.Mp p = (∏ p, B.localVolumeAtPlace p) * (∏ p, B.μKp p) * (∏ p, B.μKnatp p) /
      ((∏ p, B.μSp p) * ∏ p, B.μSp' p) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff qU.ne'] at h
    rw [h]; field_simp
  have hKn : ∏ p, B.μKnatp p = B.Gam1 * ∏ p, B.μKppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => middle_level_volume_index P B hP0 hI p
  have hSp : ∏ p, B.μSp p = B.Gam1 * ∏ p, B.μSppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.1
  have hSp' : ∏ p, B.μSp' p = B.Gam1 * ∏ p, B.μSppp' p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.2
  have a1 : 0 < ∏ p, B.localVolumeAtPlace p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have a2 : 0 < ∏ p, B.μKp p := prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have a3 : 0 < ∏ p, B.μKppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1
  have a4 : 0 < ∏ p, B.μSppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have a5 : 0 < ∏ p, B.μSppp' p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKpp MassData.μSpp MassData.μSpp' MassData.μKnat MassData.μS MassData.μS'
  rw [hM, hMo, hKn, hSp, hSp']
  constructor <;> field_simp <;> ring

theorem jacobian_natural_measure_constant : JacobianConstant := by
  intro P _ B hP hJ hNu
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  rw [hJ, hNu]
  field_simp

theorem form_signature_bound : SigBound := by
  intro P _ B hP hF hK hMs hD hA hJ hNu hI
  have hP0 := hP
  have hU := unit_level_volume_pos hP
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hKV, hKt⟩ := hK
  have hc0 : 0 < B.c0 := by unfold MassData.c0; exact div_pos (mul_pos xvN xvH) xpi
  have hc0' : 0 < B.c0' := by unfold MassData.c0'; exact div_pos (mul_pos xvN' xvH') xpi'
  have he1 : 0 ≤ B.e1 := xsd.trans hD
  have hAA : 0 < B.AA := by
    unfold MassData.AA; exact div_pos (mul_pos (mul_pos xB xC) (div_pos hMM xZZ)) hμK
  have hJc := jacobian_natural_measure_constant P B hP0 hJ hNu
  have hIntN : B.IntN ≤ B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg) := by
    rw [hJc]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (div_nonneg xZZ.le hU.le) (inv_nonneg.mpr xC.le))
  have hKt2 : B.KtopV ≤ (1 + B.δ) * B.IntN / (B.c0 * B.c0') := by
    rw [le_div_iff₀ (mul_pos hc0 hc0')]
    calc B.KtopV * (B.c0 * B.c0') = B.Smod := by unfold MassData.Smod; ring
      _ ≤ _ := hA
  have hEA : 0 ≤ B.e1 * B.AA := mul_nonneg he1 hAA.le
  calc B.Sig = B.ρ0 * B.KV := hF
    _ ≤ B.ρ0 * (B.e1 * B.n0c * B.KtopV) := by
        apply mul_le_mul_of_nonneg_left _ xr.le
        calc B.KV ≤ B.supdens * B.n0c * B.KtopV := hKV
          _ ≤ B.e1 * B.n0c * B.KtopV :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD xn0.le) hKt
    _ = B.e1 * B.AA * B.KtopV := by rw [← hMs]; ring
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * B.IntN / (B.c0 * B.c0')) :=
        mul_le_mul_of_nonneg_left hKt2 hEA
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg)) /
          (B.c0 * B.c0')) := by
        apply mul_le_mul_of_nonneg_left _ hEA
        apply div_le_div_of_nonneg_right _ (mul_pos hc0 hc0').le
        exact mul_le_mul_of_nonneg_left hIntN (by linarith)
    _ = _ := by
        unfold MassData.AA
        have := hc0.ne'; have := hc0'.ne'
        field_simp

theorem mass_formula_constant_one : MainTheorem := by
  intro P _ B hP h2A hF hK hMs hD hA hJ hNu hI hV hL hM hC hO hT hIx
  have hSB := form_signature_bound P B hP hF hK hMs hD hA hJ hNu hI
  obtain ⟨_, cd, cc, _, cd', cc'⟩ := column_identity P B hP hV hL hM hC
  obtain ⟨hLP, _⟩ := local_ratio_product P B hP hO hT hIx
  have htt := pos_tt hP
  have hG1 := gamma_product_pos hP
  have hμK := pos_μK hP
  have hKpp := pos_μKpp hP
  have hSpp := pos_μSpp hP
  have hSpp' := pos_μSpp' hP
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hGS : B.GS = B.tt * B.Gam1 * B.Sig := by
    unfold MassData.GS; rw [hF, cd]; field_simp
  have key : B.tt * B.Gam1 * ((1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) /
      (B.μK * B.deg)) = (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have e1 : B.MM / B.unitLevelVolume = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') * B.μK := by
      rw [← hLP]; field_simp
    have e2 : (B.c0)⁻¹ = B.d * B.μSpp / B.volHa := by rw [← cc, one_div]
    have e3 : (B.c0')⁻¹ = B.d' * B.μSpp' / B.volHa' := by rw [← cc', one_div]
    have e4 : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hV.1
    unfold MassData.Dstar
    rw [mul_inv, e1, e2, e3, e4]
    field_simp
  refine ⟨hGS, ?_, ?_⟩
  · rw [hGS, ← key]
    exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le
  · calc B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig := h2A
      _ ≤ _ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le

theorem dual_density_explicit_form : DstarProductFormula := by
  intro P _ B hP hI
  have hKpp := pos_μKpp hP
  have hidx := pos_idx hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hK : B.μK = (∏ p, B.gg p / (B.nn p * B.uk p)) * B.μKpp := by
    unfold MassData.μK MassData.μKpp
    have : ∏ p, B.μKp p = ∏ p, (B.gg p / (B.nn p * B.uk p) * B.μKppp p) :=
      prod_congr rfl fun p _ => (hI p).1
    rw [this, prod_mul_distrib]; ring
  unfold MassData.Dstar MassData.V0
  rw [hK]
  field_simp

theorem density_explicit_form : NN0Formula := by
  intro P _ B hP hV hL hM hO hT hI
  obtain ⟨_, hLP⟩ := local_ratio_product P B hP hO hT hI
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  have hU := unit_level_volume_pos hP
  have hS := pos_μS hP
  have hS' := pos_μS' hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hVB, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, _, hLS', _⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  have hKn : B.μKnat = B.μK * ∏ p, B.glk p * B.nn p / B.gg p := by
    unfold MassData.μKnat MassData.μK
    have : ∏ p, B.μKnatp p = ∏ p, (B.μKp p * (B.glk p * B.nn p / B.gg p)) :=
      prod_congr rfl fun p _ => by
        obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
        have h := (hI p).2
        rw [div_eq_iff qKp.ne'] at h
        rw [h]; ring
    rw [this, prod_mul_distrib]; ring
  have e1 : B.MM = B.μKnat / (B.μS * B.μS') * B.μK * B.unitLevelVolume := by
    rw [← hLP]; field_simp
  have eB : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hVB
  unfold MassData.nn0 MassData.V0
  rw [e1, hKn, eB, hρ, hρ', eN, eN', hLS, hLS']
  field_simp

theorem density_final_sum : VolumeMassSum := by
  intro P _ B hP hV hL hM hC hI
  have hG1p := gamma_product_pos hP
  have hKpp := pos_μKpp hP
  have hidx := pos_idx hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hρ, _, hρ', _⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have hK : B.μK = (∏ p, B.gg p / (B.nn p * B.uk p)) * B.μKpp := by
    unfold MassData.μK MassData.μKpp
    have : ∏ p, B.μKp p = ∏ p, (B.gg p / (B.nn p * B.uk p) * B.μKppp p) :=
      prod_congr rfl fun p _ => (hI p).1
    rw [this, prod_mul_distrib]; ring
  have hprod : (∏ p, B.ga p * (B.glk p * B.nn p) / B.gg p) =
      B.Gam1 * ∏ p, B.glk p * B.nn p / B.gg p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => by ring
  have hI2 : (∏ p, B.glk p * B.nn p / B.gg p) * (∏ p, B.gg p / (B.nn p * B.uk p)) = B.Gam1 := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    unfold MassData.ga
    field_simp
  have hd2 : B.d = B.Gam1 * B.ρ0 * B.dimπ := by rw [hdd, ← hG1, hρ]; field_simp
  have hd2' : B.d' = B.Gam1 * B.ρ0' * B.dimπ' := by rw [hdd', ← hG1', hρ']; field_simp
  unfold MassData.V0 MassData.Dstar
  rw [hprod, hK, hd2, hd2', ← hI2]
  field_simp

end Formalism.FourierDecayAlt.P
