import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair

namespace Formalism.FourierDecayAlt.P.PBF

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.JCx2
open scoped ENNReal NNReal Matrix

noncomputable section

section law

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zeta_sec (Bs : B.RealPlaceData k r Wp Wq) {ζ : ℂ} (hζ : Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq ζ) :
    Q.zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r (Bs.μsec ζ)) = ζ := by
  have hsec := Bs.sec.2 ζ hζ
  have e : herm (Hpk k r) (bigCell k r (fun _ => 1) (Bs.μsec ζ) *ᵥ Bs.z') Bs.z =
      Q.zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r (Bs.μsec ζ)) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  rw [← e, Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ Bs.z_mem Bs.z'_mem, hsec.2]

theorem measurable_zetaM (Bs : B.RealPlaceData k r Wp Wq) :
    Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
  (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable

theorem measurable_Psi (Bs : B.RealPlaceData k r Wp Wq) :
    Measurable (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec) :=
  rb_measurable_Psi fun i j => (Bs.sec.1 i j).continuousOn

theorem rbP_map_zeta (Bs : B.RealPlaceData k r Wp Wq) :
    ((rbP k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μW Bs.μW').map (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec)).map
        (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      (Bs.μW Set.univ * Bs.μW' Set.univ) • (volume : Measure ℂ).withDensity (rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
  have := B7.sf Bs.haarW
  have := B7.sf Bs.haarW'
  have hz := measurable_zetaM Bs
  have hΨ := measurable_Psi Bs
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  have e2 : ∫⁻ a, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of a))
      ∂((rbP k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μW Bs.μW').map (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec)) =
      ∫⁻ a, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec a)))
        ∂(rbP k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μW Bs.μW') := lintegral_map (hψ.comp hz) hΨ
  rw [lintegral_map hψ hz, e2, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_radial_weight k _ _) hψ]
  unfold rbP
  have hFm : Measurable (fun a : ℂ × (Mt k r × Mt k r) => ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r)
      (Matrix.of (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec a)))) := (hψ.comp hz).comp hΨ
  refine (lintegral_prod _ hFm.aemeasurable).trans ?_
  refine (lintegral_withDensity_eq_lintegral_mul _ (measurable_radial_weight k _ _) hFm.lintegral_prod_right').trans ?_
  have hae : ∀ᵐ p ∂(Bs.μW.prod Bs.μW'), Matrix.of p.1 ∈ UWset k r Bs.z ∧ Matrix.of p.2 ∈ UWset k r Bs.z' := by
    have h1 : Bs.μW (UWset k r Bs.z)ᶜ = 0 := Bs.haarW.conc
    have h2 : Bs.μW' (UWset k r Bs.z')ᶜ = 0 := Bs.haarW'.conc
    rw [ae_iff]
    refine measure_mono_null (t := ((UWset k r Bs.z)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (UWset k r Bs.z')ᶜ)) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, not_and_or] at hp
      rcases hp with h | h
      · exact Or.inl ⟨h, trivial⟩
      · exact Or.inr ⟨trivial, h⟩
    · refine measure_union_null ?_ ?_
      · exact (Measure.prod_prod _ _).trans (mul_eq_zero_of_left h1 _)
      · exact (Measure.prod_prod _ _).trans (mul_eq_zero_of_right _ h2)
  rw [smul_eq_mul, ← lintegral_const_mul _ ((measurable_radial_weight k _ _).mul hψ)]
  refine lintegral_congr_ae ?_
  filter_upwards [rb_ae_ne_circle (mul_pos Bs.T_pos Bs.T'_pos)] with ζ hζ
  simp only [Pi.mul_apply]
  by_cases h : ζ ∈ rbO (Tz k r Bs.z) (Tz k r Bs.z')
  · have hin : ∫⁻ p, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r)
        (Matrix.of (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec (ζ, p)))) ∂(Bs.μW.prod Bs.μW') =
        ∫⁻ _p, ψ ζ ∂(Bs.μW.prod Bs.μW') := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [rb_Psi_eq h]
      have hi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hp.1
      show ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) ((Matrix.of p.1)⁻¹ * B2.embWb k r (Bs.μsec ζ) * Matrix.of p.2)) = ψ ζ
      rw [Formalism.FourierDecayAlt.P.Qx5.zeta_inv hi hp.2, zeta_sec Bs h]
    rw [hin, lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod]
    ring
  · have h0 : rbW k (Tz k r Bs.z) (Tz k r Bs.z') ζ = 0 := by
      unfold rbW; rw [rb_zWeight_zero_of_not h hζ, ENNReal.ofReal_zero]
    simp [h0]

end law

end

section one

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem weight_annulus (k : ℕ) {T T' : ℝ} (hTT : 0 ≤ T * T') :
    let A : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < T * T' + 1}
    0 < (volume.withDensity (rbW k T T')) A ∧ (volume.withDensity (rbW k T T')) A < ∞ := by
  intro A
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const Complex.continuous_normSq.measurable).inter
      (measurableSet_lt Complex.continuous_normSq.measurable measurable_const)
  rw [withDensity_apply _ hAm]
  constructor
  · let A' : Set ℂ := {ζ | T * T' + 1 / 2 < Complex.normSq ζ ∧ Complex.normSq ζ < T * T' + 1}
    have hA'o : IsOpen A' := (isOpen_lt continuous_const Complex.continuous_normSq).inter
      (isOpen_lt Complex.continuous_normSq continuous_const)
    have hA'A : A' ⊆ A := fun ζ h => ⟨by linarith [h.1], h.2⟩
    have hne : A'.Nonempty := by
      obtain ⟨x, hx⟩ : ∃ x : ℝ, 0 ≤ x ∧ x ^ 2 = max 0 (T * T' + 3 / 4) := ⟨Real.sqrt _, Real.sqrt_nonneg _,
        Real.sq_sqrt (le_max_left _ _)⟩
      refine ⟨(x : ℂ), ?_, ?_⟩ <;> simp only [Complex.normSq_ofReal] <;> rw [← sq, hx.2] <;>
        [exact lt_of_lt_of_le (by linarith) (le_max_right _ _); skip]
      rcases le_total 0 (T * T' + 3 / 4) with h | h
      · rw [max_eq_right h]; linarith
      · exfalso; linarith
    have hpos : 0 < volume A' := hA'o.measure_pos volume hne
    have hc : 0 < ENNReal.ofReal ((1 / 2 : ℝ) ^ (k - 1)) := ENNReal.ofReal_pos.2 (by positivity)
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ (k - 1)) * volume A' := ENNReal.mul_pos hc.ne' hpos.ne'
      _ = ∫⁻ _ in A', ENNReal.ofReal ((1 / 2 : ℝ) ^ (k - 1)) := by rw [setLIntegral_const]
      _ ≤ ∫⁻ ζ in A', rbW k T T' ζ := by
        refine setLIntegral_mono (measurable_radial_weight k _ _) fun ζ hζ => ?_
        unfold rbW B2.zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num) (by linarith [hζ.1]) _)
      _ ≤ ∫⁻ ζ in A, rbW k T T' ζ := lintegral_mono_set hA'A
  · calc ∫⁻ ζ in A, rbW k T T' ζ ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) := by
          refine setLIntegral_mono measurable_const fun ζ hζ => ?_
          unfold rbW B2.zWeight
          rw [if_pos hζ.1.le]
          rw [ENNReal.ofReal_le_one]
          exact pow_le_one₀ (by linarith [hζ.1]) (by linarith [hζ.2])
      _ = volume A := by rw [setLIntegral_const, one_mul]
      _ ≤ volume (Metric.closedBall (0 : ℂ) (Real.sqrt (|T * T'| + 1))) := by
          refine measure_mono fun ζ hζ => ?_
          rw [Metric.mem_closedBall, dist_zero_right]
          rw [← Real.sqrt_sq (norm_nonneg ζ)]
          refine Real.sqrt_le_sqrt ?_
          rw [Complex.sq_norm]
          linarith [hζ.2, le_abs_self (T * T')]
      _ < ∞ := measure_closedBall_lt_top

theorem const_one (Bs : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (C : ℝ≥0)
    (hmap : μ = (C : ℝ≥0∞) • (rbP k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μW Bs.μW').map
      (rbPsi k r (Tz k r Bs.z) (Tz k r Bs.z') Bs.μsec)) (hZ : KB.ZetaNorm Bs μ) :
    (C : ℝ≥0∞) * (Bs.μW Set.univ * Bs.μW' Set.univ) = 1 := by
  have h1 := Formalism.FourierDecayAlt.P.PBO.zetaNorm_map hZ
  have h2 : μ.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      ((C : ℝ≥0∞) * (Bs.μW Set.univ * Bs.μW' Set.univ)) •
        (volume : Measure ℂ).withDensity (rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
    rw [hmap, Measure.map_smul, rbP_map_zeta, smul_smul]
  rw [h1] at h2
  obtain ⟨hp, hf⟩ := weight_annulus k (T := Tz k r Bs.z) (T' := Tz k r Bs.z') (mul_pos Bs.T_pos Bs.T'_pos).le
  set A : Set ℂ := {ζ | Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq ζ ∧
    Complex.normSq ζ < Tz k r Bs.z * Tz k r Bs.z' + 1}
  have h3 := congrArg (fun ν : Measure ℂ => ν A) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have := (ENNReal.mul_eq_right hp.ne' hf.ne).1 h3.symm
  exact this

end one

section formOne

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_one (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (hZ : KB.ZetaNorm D μ)
    (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π')
    (hΦ : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2)
    (hΦ' : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2)
    (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    P5.pairAt μ Φ Φ' c = ((1 : ℝ) : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))) := by
  have hμb : B.IsHaarOn (B2.UWb k r) μ := by
    rw [rb_uwb_eq]
    exact hZ.1
  obtain ⟨C, hC, hmap⟩ := rb_map D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec hμb D.haarW D.haarW'
  have h1 := const_one D μ C hmap hZ
  have hfW : IsFiniteMeasure D.μW := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z_mem D.T_pos D.haarW
  have hfW' : IsFiniteMeasure D.μW' := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z'_mem D.T'_pos D.haarW'
  have hCm : (C : ℝ) * (D.μW.prod D.μW').real Set.univ = 1 := by
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at h2
    rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    exact h2
  have key : P5.pairAt μ Φ Φ' c = (((C : ℝ) * (D.μW.prod D.μW').real Set.univ : ℝ) : ℂ) *
      ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))) := by
    unfold P5.pairAt
    exact rb_integral D.T_pos D.T'_pos D.sec D.haarW D.haarW' hmap _ (rb_pair_sm Φ Φ' c) _
      (fun ζ hζ x y hx hy => rb_point D F F' Φ Φ' hΦ hΦ' hc hζ hx hy)
  rw [key, hCm]

end formOne

section exist

theorem haar_smul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) : B.IsHaarOn U (c • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcT) (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => c⁻¹ • ν) h0
    simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hcT] using this

theorem zetaNormExists : Formalism.FourierDecayAlt.P.PBO.ZetaNormExists := by
  intro k r Wp Wq _ _ _ _ Bs
  obtain ⟨μb, hb⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨C, hC, hmap⟩ := rb_map Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec hb Bs.haarW Bs.haarW'
  have hfW : IsFiniteMeasure Bs.μW := RankOneEmbeddings.R1.haar_finite B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  have hfW' : IsFiniteMeasure Bs.μW' := RankOneEmbeddings.R1.haar_finite B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  set a : ℝ≥0∞ := (C : ℝ≥0∞) * (Bs.μW Set.univ * Bs.μW' Set.univ) with ha
  have ha0 : a ≠ 0 := by
    refine (ENNReal.mul_pos (by exact_mod_cast hC.ne') (ENNReal.mul_pos ?_ ?_).ne').ne'
    · exact Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero
    · exact Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero
  have haT : a ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  have hlaw : μb.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      a • (volume : Measure ℂ).withDensity (rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
    rw [hmap, Measure.map_smul, rbP_map_zeta, smul_smul]
  refine ⟨a⁻¹ • μb, ?_, fun ψ hψ => ?_⟩
  · rw [Formalism.FourierDecayAlt.P.PBH.glev_last_eq]
    exact haar_smul hb (ENNReal.inv_ne_zero.2 haT) (ENNReal.inv_ne_top.2 ha0)
  · rw [lintegral_smul_measure, ← lintegral_map hψ (measurable_zetaM Bs), hlaw, lintegral_smul_measure,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_radial_weight k _ _) hψ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel ha0 haT, one_mul]
    rfl

end exist

section formOneThm

theorem formOne : Formalism.FourierDecayAlt.P.PBO.FormOne := by
  intro Wp Wq _ _ _ _ _ _ P0 T j X μ L st l0 hD hZ w F F' Φ Φ' ε hε hF hF' hΦ hΦ'
  have hN := Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF
  have hPic : ∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (P5.act (P5.RRi L st 0 (D.positionted w)) Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _)
          (B.JF (T.bs j) (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F a)) y.1 y.2 := by
    intro a y hy
    rw [Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w (fun b => B.JF (T.bs j) (F b)) Φ
      (fun b => Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (F b) ε hε (hF b)) hΦ a y hy]
    exact (Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF a y hy).symm
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main (T.bs j) μ 1
    (fun G G' Ψ Ψ' hΨ hΨ' c hc => pairAt_one (T.bs j) μ hZ G G' Ψ Ψ' hΨ hΨ' c hc)
    (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F) F' (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ'
    (fun a => (hN a).2.1) (fun a => (hF' a).2.1) hPic hΦ'
  refine Eq.trans ?_ h.symm
  simp only [Complex.ofReal_one, one_mul]
  rfl

end formOneThm

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

theorem module_form_eq_radial_form_one : Formalism.FourierDecayAlt.P.PBO.FormOne := PBF.formOne

theorem exists_zeta_normalized_haar : Formalism.FourierDecayAlt.P.PBO.ZetaNormExists := PBF.zetaNormExists

end Formalism.FourierDecayAlt.P
