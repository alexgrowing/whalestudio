import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ShellFD

theorem isFundamentalDomain_shell : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hT0 : 0 < T := one_pos.trans hT1
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hTe : Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) = T ^ (-1 : ℤ) := by
    rw [hT, Real.exp_one_pow, _root_.zpow_neg_one, ← Real.exp_neg]
    push_cast
    rfl
  have hcomm : ∀ (n : ℤ) g, splitCentre E a 1 ^ n * g = g * splitCentre E a 1 ^ n := fun n g => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
    exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ g
  have hTadd : ∀ m n : ℤ, T ^ m * T ^ n = T ^ (m + n) := fun m n => (zpow_add₀ hT0.ne' m n).symm
  rw [hTe]
  refine
    { nullMeasurableSet := h𝓕.nullMeasurableSet.inter
        ((measurableSet_lt measurable_const hδc.measurable).inter
          (measurableSet_le hδc.measurable measurable_const)).nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have hN := ae_iff.1 h𝓕.ae_covers
    have hB : μ (⋃ n : ℤ, (fun x => splitCentre E a 1 ^ n * x) ⁻¹'
        {x | ¬∃ γ : (ratGL E a).range, γ • x ∈ 𝓕}) = 0 :=
      measure_iUnion_null fun n => (measurePreserving_mul_left μ _).quasiMeasurePreserving.preimage_null hN
    refine Filter.mem_of_superset (compl_mem_ae_iff.2 hB) fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_not] at hx
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow (hδ0 x) hT1
    obtain ⟨γ, hγ⟩ := not_forall_not.1 (hx (-(m + 1)))
    obtain ⟨γ0, hγ0⟩ := γ.2
    refine ⟨⟨(γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)),
      mul_mem (Subgroup.mem_sup_left γ.2) (GlobalTheory.CuspRep.CuspidalL2GL.zpow_mem_latticeGL _)⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.smul_def]
      simpa only [Subgroup.smul_def, smul_eq_mul, mul_assoc] using hγ
    · rw [Subgroup.smul_def]
      change T ^ (-1 : ℤ) < δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x)
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-1 : ℤ) = T ^ (-(m + 1)) * T ^ m := by rw [hTadd]; ring_nf
        _ < T ^ (-(m + 1)) * δ x := mul_lt_mul_of_pos_left hm1 (zpow_pos hT0 _)
    · rw [Subgroup.smul_def]
      change δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x) ≤ 1
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-(m + 1)) * δ x ≤ T ^ (-(m + 1)) * T ^ (m + 1) := mul_le_mul_of_nonneg_left hm2 (zpow_pos hT0 _).le
        _ = 1 := by rw [hTadd]; simp
  · intro g1 g2 hne
    have key : ∀ (g : latticeGL E a) (γ : GL (Fin a) E) (n : ℤ),
        ratGL E a γ * splitCentre E a 1 ^ n = g → ∀ y ∈ g • (𝓕 ∩ {g | T ^ (-1 : ℤ) < δ g ∧ δ g ≤ 1}),
        T ^ (n - 1) < δ y ∧ δ y ≤ T ^ n ∧
          y ∈ splitCentre E a 1 ^ n • ((⟨ratGL E a γ, γ, rfl⟩ : (ratGL E a).range) • 𝓕) := by
      rintro g γ n hg y ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
      have hy : g • x = splitCentre E a 1 ^ n * (ratGL E a γ * x) := by
        rw [Subgroup.smul_def, smul_eq_mul, ← hg, hcomm n (ratGL E a γ * x)]
        simp only [mul_assoc, hcomm n x]
      beta_reduce
      rw [hy]
      refine ⟨?_, ?_, Set.smul_mem_smul_set (Set.smul_mem_smul_set hx)⟩
      · rw [hδz, hδr]
        calc T ^ (n - 1) = T ^ n * T ^ (-1 : ℤ) := by rw [hTadd]; ring_nf
          _ < T ^ n * δ x := mul_lt_mul_of_pos_left hx1 (zpow_pos hT0 _)
      · rw [hδz, hδr]
        calc T ^ n * δ x ≤ T ^ n * 1 := mul_le_mul_of_nonneg_left hx2 (zpow_pos hT0 _).le
          _ = T ^ n := mul_one _
    obtain ⟨γ1, n1, h1⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g1.2
    obtain ⟨γ2, n2, h2⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g2.2
    by_cases hn : n1 = n2
    · subst hn
      have hγ : (⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) ≠ ⟨ratGL E a γ2, γ2, rfl⟩ := fun h => hne <|
        Subtype.ext (by rw [← h1, ← h2, show ratGL E a γ1 = ratGL E a γ2 from congrArg Subtype.val h])
      have hd : AEDisjoint μ (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) • 𝓕))
          (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ2, γ2, rfl⟩ : (ratGL E a).range) • 𝓕)) := by
        rw [AEDisjoint, ← Set.smul_set_inter, measure_smul]
        exact h𝓕.aedisjoint hγ
      exact hd.mono (fun y hy => (key g1 γ1 n1 h1 y hy).2.2) (fun y hy => (key g2 γ2 n1 h2 y hy).2.2)
    · refine Disjoint.aedisjoint (Set.disjoint_left.2 fun y hy1 hy2 => ?_)
      obtain ⟨a1, b1, -⟩ := key g1 γ1 n1 h1 y hy1
      obtain ⟨a2, b2, -⟩ := key g2 γ2 n2 h2 y hy2
      rcases lt_or_gt_of_ne hn with h | h
      · exact absurd a2 (not_lt.2 (b1.trans (zpow_le_zpow_right₀ hT1.le (by omega : n1 ≤ n2 - 1))))
      · exact absurd a1 (not_lt.2 (b2.trans (zpow_le_zpow_right₀ hT1.le (by omega : n2 ≤ n1 - 1))))

end GlobalTheory.ShellFD
