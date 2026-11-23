import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.HasseOrdBdW

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem kp_charZero (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : CharZero (Kp X la N) := by
  have := Kl_charZero X la
  exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

theorem isUnif_unifO (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hfd : FiniteDimensional (Kp X la G.N) (OsK X la G.w)) :
    IsUnif (OsK X la G.w) (unifO X la G.N) := by
  have : Algebra.IsIntegral (Kp X la G.N) (OsK X la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp X la G.N)
    (Op.irreducible_map X la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))))

theorem isDVRAt_pt (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (hP : PublishedIntClos)
    (hfd : FiniteDimensional (Kp X la G.N) (OsK X la G.w)) (hred : IsReduced (OsK X la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero (X := X) la G.N
  exact (hP (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2 ζ

theorem addPreservesExpCongruence : S3 := by
  intro D B P j X ka wL wF G la Q hP hC ζ
  obtain ⟨hfd, hred, hgen⟩ := hC
  have hU := isUnif_unifO G la hfd
  have := isDVRAt_pt G la hP hfd hred ζ
  refine ⟨ordV_zero Q.c ζ hU hgen, fun m v => ?_⟩
  show ordV (unifO X la G.N) ζ Q.e Q.c v ≤ ordV (unifO X la G.N) ζ Q.e Q.c (m • v)
  rw [← Int.cast_smul_eq_zsmul (OsK X la G.w) m v, ordV_smul Q.c ζ hU hgen]
  exact le_add_of_nonneg_left (ord_nonneg ζ hU (intCast_mem _ m))

theorem expCongruenceExtendsToSum : S4 := by
  intro e vf vg d T n hvf h
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast Nat.zero_le e)
  have e1 : (T : EReal) * (d : EReal) = ((T * d : ℝ) : EReal) := by rw [EReal.coe_mul]; rfl
  have e2 : ((T + n : ℕ) : EReal) * (d : EReal) = ((((T + n : ℕ) : ℝ) * d : ℝ) : EReal) := by
    rw [EReal.coe_mul]; rfl
  rw [e1, e2]
  induction vf using EReal.rec with
  | bot => exact absurd rfl hvf
  | top =>
    have hg : vg = ⊤ := by
      rw [EReal.top_add_coe] at h
      exact top_le_iff.mp h
    rw [hg, EReal.top_sub_coe, EReal.top_sub_coe]
  | coe a =>
    induction vg using EReal.rec with
    | bot =>
      rw [← EReal.coe_add] at h
      exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
    | top =>
      rw [EReal.top_sub_coe]
      exact le_top
    | coe b =>
      have h' : a + n * d ≤ b := by
        rw [← EReal.coe_add] at h
        exact EReal.coe_le_coe_iff.mp h
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      push_cast
      nlinarith

end PI.HasseOrdBdW
