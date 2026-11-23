import Formalism.HermitianCurvature.StatementJCCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.JCx5

section partE

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx4

theorem me_approx_one_cpt {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (mm m0 : ℕ) (hm0 : m0 ≤ mm) (A' : ℝ) (hA' : 0 ≤ A') (F : Mat k r → E) (hF : CkOn (mm : ℕ∞) (GV k r) F)
    (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) (hε : 0 < ε) (hsupp : ∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g)
    (R τ : ℝ) (hR : 0 < R) (hτ : 0 < τ) :
    ∃ y : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) y ∧ (∀ (A'' : ℝ) (m' : ℕ), InCC A'' m' y) ∧
      (∀ g ∈ GV k r, y g ≠ 0 → ε / 4 ≤ Gf k r z z' g) ∧
      CCle A' m0 (fun g => pdPhi (R⁻¹ • g) • F g - y g) τ ∧ HasCompactSupport y := by
  haveI : ProperSpace (Mat k r) := FiniteDimensional.proper_real _
  obtain ⟨X, hXc, hXs, hXe, hXQ⟩ := extend mm F hF z z' ε hε hsupp R hR
  obtain ⟨Cb, hCb0, hCb⟩ := dlr_bound (k := k) (r := r) (E := E) m0
  obtain ⟨ρX, hρX⟩ : ∃ ρX : ℝ, ∀ g, X g ≠ 0 → ‖g‖ ≤ ρX := by
    obtain ⟨ρ, hρ⟩ := hXs.isCompact.isBounded.subset_closedBall (0 : Mat k r)
    exact ⟨ρ, fun g hg => by simpa using hρ (subset_tsupport _ hg)⟩
  have hBc : IsCompact (Metric.closedBall (0 : Mat k r) (ρX + 1)) := isCompact_closedBall _ _
  have hGf : Continuous fun g : Mat k r => Gf k r z z' g := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z'
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.1
    (hBc.uniformContinuousOn_of_continuous hGf.continuousOn) (ε / 4) (by positivity)
  have hgN : Continuous fun g : Mat k r => gN g := by unfold gN; fun_prop
  have hWc : Continuous fun g : Mat k r => gN g ^ A' * (1 + ‖g‖) ^ m0 :=
    ((Real.continuous_rpow_const hA').comp hgN).mul (by fun_prop)
  obtain ⟨W₀, hW₀⟩ := hBc.exists_bound_of_continuousOn hWc.continuousOn
  set W : ℝ := max W₀ 0 with hWdef
  have hW : 0 ≤ W := le_max_right _ _
  have hden : 0 < Cb * W * (m0 + 1) + 1 := by
    have : 0 ≤ Cb * W * ((m0 : ℝ) + 1) := mul_nonneg (mul_nonneg hCb0 hW) (by positivity)
    linarith
  set η : ℝ := τ / (Cb * W * (m0 + 1) + 1) with hηdef
  have hη : 0 < η := div_pos hτ hden
  have hCbη : Cb * W * (m0 + 1) * η ≤ τ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith
  have hm0' : ((m0 : ℕ∞) : WithTop ℕ∞) ≤ ((mm : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (by exact_mod_cast hm0)
  have htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n => WithTop.coe_le_coe.2 le_top
  obtain ⟨y, hys, hyc, hysupp, hyd⟩ := mollify m0 X (hXc.of_le hm0') hXs η (min 1 δ₁) hη (lt_min one_pos hδ₁)
  have hyB : ∀ g, y g ≠ 0 → ‖g‖ < ρX + 1 := by
    intro g hg
    obtain ⟨g', hd, hX'⟩ := hysupp g hg
    have h1 := hρX g' hX'
    have h2 : ‖g‖ ≤ ‖g'‖ + ‖g - g'‖ := by
      have := norm_add_le g' (g - g')
      simpa using this
    rw [dist_eq_norm] at hd
    have h3 : ‖g - g'‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    linarith
  refine ⟨y, fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro A'' m'
    refine Formalism.FourierDecayAlt.P.compact_support_finite_class k r E y (Metric.closedBall 0 (ρX + 1))
      (fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩) hBc (fun g hg => ?_) A'' m'
    by_contra h
    exact hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))
  · intro g _ hy0
    obtain ⟨g', hd, hX'⟩ := hysupp g hy0
    have h1 := hXQ g' hX'
    have hg'B : g' ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) :=
      mem_closedBall_zero_iff.2 (by linarith [hρX g' hX'])
    have hgB : g ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) := mem_closedBall_zero_iff.2 (le_of_lt (hyB g hy0))
    have h2 := hδ₁' g hgB g' hg'B (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h2
    linarith [h2.2]
  · have hXY : CCle A' m0 (fun g => X g - y g) τ := by
      have hcd : ContDiff ℝ ((m0 : ℕ∞) : WithTop ℕ∞) (fun g => X g - y g) := (hXc.of_le hm0').sub (hys.of_le (htop m0))
      refine ⟨fun g₀ _ => ⟨Set.univ, fun g => X g - y g, isOpen_univ, trivial, hcd.contDiffOn, fun _ _ _ => rfl⟩, ?_⟩
      intro u v hu hv hl g _
      have hb := hCb (fun g => X g - y g) hcd u v hu hv hl g
      have hgN0 : 0 ≤ gN g ^ A' := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      by_cases hgB : ‖g‖ ≤ ρX + 1
      · have hi : ∀ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ η := by
          intro i hi
          have hi' : i ≤ m0 := by simpa [Nat.lt_succ_iff] using hi
          have e1 : iteratedFDeriv ℝ i (fun g => X g - y g) g = iteratedFDeriv ℝ i X g - iteratedFDeriv ℝ i y g :=
            iteratedFDeriv_sub_apply ((hXc.of_le (le_trans (WithTop.coe_le_coe.2 (by exact_mod_cast hi')) hm0')).contDiffAt)
              ((hys.of_le (htop i)).contDiffAt)
          rw [e1, norm_sub_rev]
          exact hyd i hi' g
        have hsum : ∑ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ (m0 + 1) * η := by
          have := Finset.sum_le_card_nsmul _ _ _ hi
          simpa [Finset.card_range, nsmul_eq_mul] using this
        have hWg : gN g ^ A' * (1 + ‖g‖) ^ m0 ≤ W := by
          have := hW₀ g (mem_closedBall_zero_iff.2 hgB)
          exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))
        have h1p : 0 ≤ (1 + ‖g‖) ^ m0 := by positivity
        calc gN g ^ A' * ‖dLR u v (fun g => X g - y g) g‖
            ≤ gN g ^ A' * (Cb * (1 + ‖g‖) ^ m0 * ((m0 + 1) * η)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hCb0 h1p))) hgN0
          _ = Cb * (gN g ^ A' * (1 + ‖g‖) ^ m0) * (m0 + 1) * η := by ring
          _ ≤ Cb * W * (m0 + 1) * η := by
              have : 0 ≤ ((m0 : ℝ) + 1) * η := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hWg hCb0]
          _ ≤ τ := hCbη
      · have hev : (fun g => X g - y g) =ᶠ[nhds g] fun _ => (0 : E) := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (not_le.1 hgB)] with g' hg'
          have hX0 : X g' = 0 := by
            by_contra h
            have := hρX g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          have hy0 : y g' = 0 := by
            by_contra h
            have := hyB g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          simp [hX0, hy0]
        have hz : ∀ i, iteratedFDeriv ℝ i (fun g => X g - y g) g = 0 := by
          intro i
          rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
          simp
        simp only [hz, norm_zero, Finset.sum_const_zero, mul_zero] at hb
        have : ‖dLR u v (fun g => X g - y g) g‖ = 0 := le_antisymm hb (norm_nonneg _)
        rw [this, mul_zero]
        exact hτ.le
    exact Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => by simp only [hXe g hg]) hXY
  · refine HasCompactSupport.intro hBc fun g hg => ?_
    by_contra h
    exact hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))

end partE

end Formalism.FourierDecayAlt.P.JCx5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx4 Formalism.FourierDecayAlt.P.JCx5

theorem positive_density_compact_support : Formalism.FourierDecayAlt.JC.PosDensityCpt := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε hε hA hmm H x hx
  have hm0 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hAB := pd_thr_AB P0 j w.length A hA
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hAB0 : 0 < AB P0.k (P0.r - (j : ℕ)) := by unfold AB; positivity
  have hA1 : 0 ≤ A - 1 := by linarith

  choose cx hcx using fun a => (hx a).2.1
  have hcx0 : ∀ a, 0 ≤ cx a := fun a => pd_ccle_nonneg (hcx a)
  set c0 : ℝ := ∑ a, cx a with hc0def
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun a _ => hcx0 a
  have hX : ∀ a, CCle A mm (x a) c0 := fun a => pd_ccle_mono_c (hcx a)
    (Finset.single_le_sum (f := cx) (fun b _ => hcx0 b) (Finset.mem_univ a))
  obtain ⟨Cf, hCf0, hCf⟩ := formLev_bound_mm P0 T s j w A hA
  obtain ⟨Kc, hKc0, hKc⟩ := pd_cut_ccle (k := P0.k) (r := P0.r - j) (E := Wq →L[ℂ] Wp) mm
  refine pd_nonneg_of_approx _ (Cf * (2 * c0 + 1)) fun R hR1 => ?_
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  set τ : ℝ := 1 / R with hτdef
  have hτ : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτdef, div_le_one hR0]; exact hR1
  set R' : ℝ := max 1 (2 * Kc * c0 / τ) with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcut : Kc * c0 / R' ≤ τ / 2 := by
    rw [div_le_iff₀ hR']
    have h1 : 2 * Kc * c0 / τ ≤ R' := le_max_right _ _
    rw [div_le_iff₀ hτ] at h1
    nlinarith
  have happ := fun a => me_approx_one_cpt mm _ hm0 (A - 1) hA1 (x a) (hx a).1 (T.bs j).z (T.bs j).z' ε hε (hx a).2.2
    R' (τ / 2) hR' (by positivity)
  choose y hyck hyin hysupp hycc hycpt using happ
  have hpos := H (ε / 4) (by positivity) y fun a => ⟨⟨hyck a, hyin a, hysupp a⟩, hycpt a⟩
  set e : Wd.Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := x - y with hedef
  have he : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (e a) τ := by
    intro a
    have h1 := pd_ccle_mono le_rfl hm0 (hKc R' hR' A (x a) c0 (hX a))
    have h2 := CCle_add h1 (hycc a)
    have e2 : (fun g => pdPsi R' g • x a g + (pdPhi (R'⁻¹ • g) • x a g - y a g)) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, pdPsi, sub_smul, one_smul]
      abel
    rw [e2] at h2
    exact pd_ccle_mono_c h2 (by linarith)
  have hx1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x a) c0 :=
    fun a => pd_ccle_mono (by linarith) hm0 (hX a)
  have hy1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (y a) (c0 + τ) := by
    intro a
    have h := CCle_add (hx1 a) (CCle_smul (-1) (he a))
    have e3 : (fun g => x a g + (-1 : ℂ) • e a g) = y a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e3] at h
    simpa using h
  have hv : ∀ {F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} {c : ℝ},
      CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) F c →
      CCle (A - 1 - 2 * (w.length : ℝ)) 5 F c := fun h => pd_ccle_mono (by linarith) (by omega) h

  have hxI : ∀ a, InCC A mm (x a) := fun a => (hx a).2.1
  have hyI : ∀ a, InCC A mm (y a) := fun a => hyin a A mm
  have heI : ∀ a, InCC A mm (e a) := by
    intro a
    obtain ⟨c1, h1⟩ := hxI a
    obtain ⟨c2, h2⟩ := hyI a
    have h := CCle_add h1 (CCle_smul (-1) h2)
    have e4 : (fun g => x a g + (-1 : ℂ) • y a g) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e4] at h
    exact ⟨_, h⟩
  have hsplit : y + (1 : ℂ) • e = x := by
    funext a g
    simp only [hedef, Pi.add_apply, Pi.sub_apply, one_smul]
    abel
  have hS1 := (formLev_sesq_core P0 T s j w A mm hA hmm y e x 1 hyI heI hxI).1
  have hS2 := (formLev_sesq_core P0 T s j w A mm hA hmm y e y 1 hyI heI hyI).2
  rw [hsplit] at hS1 hS2
  refine ⟨D.formLev T s j w y y, hpos, ?_⟩
  have hb1 := hCf y e (c0 + τ) τ hy1 fun a => hv (he a)
  have hb2 := hCf e x τ c0 he fun a => hv (hx1 a)
  rw [hS1, hS2, map_one, one_mul, one_mul]
  have e5 : D.formLev T s j w y y + D.formLev T s j w y e + D.formLev T s j w e x - D.formLev T s j w y y =
      D.formLev T s j w y e + D.formLev T s j w e x := by ring
  rw [e5]
  calc ‖D.formLev T s j w y e + D.formLev T s j w e x‖
      ≤ ‖D.formLev T s j w y e‖ + ‖D.formLev T s j w e x‖ := norm_add_le _ _
    _ ≤ Cf * (c0 + τ) * τ + Cf * τ * c0 := add_le_add hb1 hb2
    _ ≤ Cf * (2 * c0 + 1) * τ := by nlinarith [mul_nonneg hCf0 hτ.le]
    _ = Cf * (2 * c0 + 1) / R := by rw [hτdef]; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt
open scoped ComplexOrder

theorem theorem_P_module_compact_support : Formalism.FourierDecayAlt.JC.ThmPModuleOfActualCpt := by
  intro hP hRMF hPD hSesq Wp Wq _ _ _ _ _ _ P0 T l0 N admitted A mm hl0 hl0k hAdmN hA hmm hdata
  refine ⟨fun j => JCx2.KKcM (T.bs j) A mm, fun j w hw => ?_, fun j F ε hε hF hF1 hF3 => ⟨ε, hε, hF1, hF, hF3⟩⟩
  have hlen := hAdmN w hw
  have hA' : P5.Auser P0 w.length + 1 ≤ A := le_trans (by linarith [JCx2.auser_mono P0 hlen]) hA
  have hmm' : P5.mmUser P0 w.length ≤ mm := le_trans (JCx2.mmUser_mono P0 hlen) hmm
  have hmemK : ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      x ∈ Submodule.pi Set.univ (fun _ => JCx2.KKcM (T.bs j) A mm) →
      ∃ ε, 0 < ε ∧ ∀ a, JC.CCCoefM (T.bs j) A mm ε (x a) := by
    intro x hx
    exact JCx2.exists_common_eps (fun a ε => JC.CCCoefM (T.bs j) A mm ε (x a))
      (fun a ε ε' _ h hF => JCx2.cCCoefM_mono h hF) (fun a => hx a (Set.mem_univ a))
  refine ⟨fun x hx x' hx' y hy c => ?_, fun x hx => ?_⟩
  · obtain ⟨e1, he1, h1⟩ := hmemK x hx
    obtain ⟨e2, he2, h2⟩ := hmemK x' hx'
    obtain ⟨e3, he3, h3⟩ := hmemK y hy
    have hε : 0 < min e1 (min e2 e3) := lt_min he1 (lt_min he2 he3)
    exact hSesq Wp Wq P0 T (M.sgn P0 l0) j w A mm _ hε hA' hmm' x x' y c
      (fun a => JCx2.cCCoefM_mono (min_le_left _ _) (h1 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_left _ _)) (h2 a))
      (fun a => JCx2.cCCoefM_mono ((min_le_right _ _).trans (min_le_right _ _)) (h3 a))
  · obtain ⟨ε, hε, hxε⟩ := hmemK x hx
    refine hPD Wp Wq P0 T (M.sgn P0 l0) j w A mm ε hε hA' hmm' ?_ x hxε
    intro ε₁ hε₁ v hvn
    obtain ⟨X, μ, L, st, hD, hOK⟩ := hdata j
    obtain ⟨Cst, hC, hform⟩ := hRMF Wp Wq P0 T j X μ L st l0 hD
    have hvn' : ∀ a, JC.NiceCoef (T.bs j) ε₁ (v a) := fun a => (hvn a).1
    have hAu : P5.Auser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ A := by
      rw [Fintype.card_fin]
      linarith [JCx2.auser_parLev P0 j w.length]
    have hmu : P5.mmUser (JC.parLev P0 j) (Fintype.card (Fin w.length)) ≤ mm := by
      rw [Fintype.card_fin]
      exact (JCx2.mmUser_parLev P0 j w.length).trans hmm'
    obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π' X μ L st l0 (T.bs j) A mm hD hl0 hl0k rfl rfl rfl rfl hAu hmu
    choose Φ hΦK hΦ using fun a => hJ (v a) ε₁ hε₁ (hvn a).1.2.1 (hvn a).2 (hvn a).1.2.2
    rw [hform w v v Φ Φ ε₁ hε₁ hvn' hvn' hΦ hΦ]
    have hpos := ((hThm (D.positionted w) (hOK w hw)).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ
      (fun a _ => hΦK a)
    have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
      hpos.trans_eq (JCx2.form_zero_indep μ _ _ _ _)
    exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P
