import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConjStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ThA

private lemma inv_mul_comm_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (a h : Matrix n n ℂ)
    (hah : a * h = h * a) : h⁻¹ * a = a * h⁻¹ := by
  by_cases hh : IsUnit h.det
  · calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hah]
      _ = a * h⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h a, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hh, Matrix.zero_mul, Matrix.mul_zero]

private lemma inv_mul_conj_mul_conj_eq_conj_of_commute {n : Type*} [Fintype n] [DecidableEq n] (a H M g M' H' : Matrix n n ℂ)
    (ha : IsUnit a.det) (c1 : a * H = H * a) (c2 : a * H' = H' * a) :
    H⁻¹ * (a * M * a⁻¹)⁻¹ * g * (a * M' * a⁻¹) * H' =
      a * (H⁻¹ * M⁻¹ * (a⁻¹ * g * a) * M' * H') * a⁻¹ := by
  have e1 : (a * M * a⁻¹)⁻¹ = a * M⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]
  have d1 : H⁻¹ * a = a * H⁻¹ := inv_mul_comm_of_mul_comm a H c1
  have d2 : a⁻¹ * H' = H' * a⁻¹ := inv_mul_comm_of_mul_comm H' a c2.symm
  rw [e1]
  simp only [Matrix.mul_assoc]
  rw [d2, ← Matrix.mul_assoc H⁻¹ a, d1, Matrix.mul_assoc]

theorem besselJ_conj {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : μW (UWset k r z)ᶜ = 0) (hN : μN (Nset k r)ᶜ = 0) (hW' : μW' (UWset k r z')ᶜ = 0)
    (a : B.Mat k r) (ha : IsUnit a.det)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a) (hc' : ∀ h ∈ UWset k r z', a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n)
    (hp' : ∀ n ∈ Nset k r, psi k r z' c (a * n * a⁻¹) = psi k r z' c' n)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (μN.map (conjM a)) μW' F g =
      besselJ k r z z' c' π π' μW μN μW' (fun x => F (a * x * a⁻¹)) (a⁻¹ * g * a) := by
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE (k := k) (r := r) a ha).measurable
  let E : Mt k r ≃ᵐ Mt k r := BesselUnitaryEquiv.conjE (k := k) (r := r) a ha
  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl (Mt k r)).prodCongr E).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr E)
  have hpm : ∀ (ν : Measure (Mt k r)) [SFinite ν],
      (ν.prod μN).map (Prod.map id (conjM a)) = ν.prod (μN.map (conjM a)) := by
    intro ν _
    rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]
  have hμ : (μW.prod (μN.map (conjM a))).prod (μW'.prod (μN.map (conjM a))) =
      ((μW.prod μN).prod (μW'.prod μN)).map Φ := by
    rw [← hpm μW, ← hpm μW', Measure.map_prod_map _ _ (measurable_id.prodMap hm) (measurable_id.prodMap hm)]
    rfl
  have aW : ∀ᵐ x ∂μW, x ∈ UWset k r z := ae_iff.2 hW
  have aN : ∀ᵐ x ∂μN, x ∈ Nset k r := ae_iff.2 hN
  have aW' : ∀ᵐ x ∂μW', x ∈ UWset k r z' := ae_iff.2 hW'
  have q1 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae aW)
  have q2 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae aN)
  have q3 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae aW')
  have q4 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae aN)
  unfold besselJ
  rw [hμ, integral_map_equiv]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2, q3, q4] with p h1 h2 h3 h4
  have hΦ : Φ p = ((p.1.1, conjM a p.1.2), (p.2.1, conjM a p.2.2)) := rfl
  have e2 : Matrix.of (conjM a p.1.2) = a * Matrix.of p.1.2 * a⁻¹ := rfl
  have e4 : Matrix.of (conjM a p.2.2) = a * Matrix.of p.2.2 * a⁻¹ := rfl
  rw [hΦ]
  dsimp only
  rw [e2, e4, hp (Matrix.of p.1.2) h2, hp' (Matrix.of p.2.2) h4,
    inv_mul_conj_mul_conj_eq_conj_of_commute a (Matrix.of p.1.1) (Matrix.of p.1.2) g (Matrix.of p.2.2) (Matrix.of p.2.1) ha
      (hc (Matrix.of p.1.1) h1) (hc' (Matrix.of p.2.1) h3)]

theorem besselJ_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW'] (t : ℝ≥0∞)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (t • μN) μW' F g =
      ((t.toReal ^ 2 : ℝ) : ℂ) • besselJ k r z z' c π π' μW μN μW' F g := by
  unfold besselJ
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, ← pow_two, Complex.coe_smul]

theorem besselJ_changeFrame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  intro k r L μsec Bs cN F hstd hR hc hκ0 hκT g
  obtain ⟨hz, hz', hπ, hπ', hμW, hμW', hμN, -⟩ := hstd
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  have hcα : L.c * (cStd / L.c) = cStd := by field_simp
  set α := cStd / L.c with hαdef
  obtain ⟨-, hT, -, -⟩ := GlobalTheory.T.besselTorusElement_properties k r α hα
  obtain ⟨hcz, hnz⟩ := hT L.z L.hz.1
  obtain ⟨hcz', hnz'⟩ := hT L.z' L.hz'.1
  have hmap := GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj k r α hα
  have ha : IsUnit (aT k r α).det := by
    rw [aT, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    split_ifs
    · exact pow_ne_zero _ hα
    · exact one_ne_zero
    · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))
  have hp : ∀ w : Fin (2 * r + k + 1) → ℂ,
      (∀ n ∈ Nset k r, ell k r w (aT k r α * n * (aT k r α)⁻¹) = α * ell k r w n) →
      ∀ n ∈ Nset k r, psi k r w L.c (aT k r α * n * (aT k r α)⁻¹) = psi k r w cStd n := by
    intro w hw n hn
    simp only [psi, hw n hn, ← mul_assoc, hcα]
  haveI : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hNc : (D.muN k r) (Nset k r)ᶜ = 0 := by rw [← hμN]; exact Bs.haarN.conc
  haveI : IsFiniteMeasureOnCompacts (D.muN k r) :=
    ⟨fun K hK => by rw [← hμN]; exact Bs.haarN.finite_compact K hK⟩
  have hW : L.μW (UWset k r L.z)ᶜ = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' (UWset k r L.z')ᶜ = 0 := L.hμW'.1.2.2.1
  have hx : 0 < ‖α‖ ^ B.kap k r := pow_pos (norm_pos_iff.mpr hα) _
  have hone : ENNReal.ofReal (‖α‖ ^ B.kap k r) * ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
  have hLμN : L.μN = (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)) •
      (D.muN k r).map (conjM (aT k r α)) := by
    rw [hmap, smul_smul, mul_assoc (L.κN * ENNReal.ofReal cN), hone, mul_one, mul_smul, ← hR.2]
    simp only [Formalism.MainNotions.S.LocBessel.μN, Formalism.MainNotions.S.haarLie, one_smul]
  have ht : (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)).toReal = lamN L cN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.1.le, ENNReal.toReal_ofReal hx.le]
    rfl
  have step : L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) •
      besselJ k r L.z L.z' L.c L.π L.π' L.μW ((D.muN k r).map (conjM (aT k r α))) L.μW' F g := by
    rw [← ht]
    show besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g = _
    rw [hLμN]
    exact besselJ_smul k r L.z L.z' L.c L.π L.π' L.μW _ L.μW' _ F g
  rw [step, besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW (D.muN k r) L.μW' hW hNc hW' (aT k r α) ha
    hcz hcz' (hp L.z fun n hn => (hnz n hn).2.2) (hp L.z' fun n hn => (hnz' n hn).2.2) F g,
    Formalism.FourierDecayAlt.B.JF, hz, hz', hπ, hπ', hμW, hμW', hμN]
  rfl

end GlobalTheory.ThA
