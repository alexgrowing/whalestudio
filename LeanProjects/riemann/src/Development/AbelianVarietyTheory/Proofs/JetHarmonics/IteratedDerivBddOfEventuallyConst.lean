import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow {e : ℕ} {φ : ℝ → ℝ} (hφ : _root_.GlobalTheory.HatNF.CutPow e φ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) ∧
      ∀ x, φ x = x ^ e * h x := by
  unfold _root_.GlobalTheory.HatNF.CutPow at hφ
  obtain ⟨hφs, ⟨δ, hδ, hφ0⟩, a, R, hφR⟩ := hφ
  have hzero : ∀ x < δ, (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => (0 : ℝ) := fun x hx =>
    (eventually_lt_nhds hx).mono fun y hy => by
      show φ y / y ^ e = 0
      rw [hφ0 y hy, zero_div]
  have hconst : ∀ x, max R δ < x → (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => a := fun x hx =>
    (eventually_gt_nhds hx).mono fun y hy => by
      have hy0 : 0 < y := hδ.trans (lt_of_le_of_lt (_root_.le_max_right _ _) hy)
      have hy1 : φ y = a * y ^ e := hφR y ((_root_.le_max_left _ _).trans hy.le)
      simp only
      rw [hy1, mul_div_assoc, div_self (pow_ne_zero _ hy0.ne'), mul_one]
  have hsmooth : ContDiff ℝ ∞ (fun y => φ y / y ^ e) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x δ with hx | hx
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
    · exact hφs.contDiffAt.div (contDiffAt_id.pow e) (pow_ne_zero _ (hδ.trans_le hx).ne')
  refine ⟨fun y => φ y / y ^ e, hsmooth, fun q => ?_, fun x => ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ (max R δ))).exists_bound_of_continuousOn
      (hsmooth.continuous_iteratedDeriv q (WithTop.coe_le_coe.mpr le_top)).continuousOn
    refine ⟨max C (max |a| 0), fun x => ?_⟩
    rcases lt_or_ge x δ with hx | hx
    · rw [(hzero x hx).iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs <;> rw [norm_zero] <;> exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
    rcases le_or_gt x (max R δ) with hx' | hx'
    · exact (hC x ⟨hx, hx'⟩).trans (_root_.le_max_left _ _)
    · rw [(hconst x hx').iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs
      · rw [Real.norm_eq_abs]; exact (_root_.le_max_left _ _).trans (_root_.le_max_right _ _)
      · rw [norm_zero]; exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
  · rcases lt_or_ge x δ with hx | hx
    · show φ x = x ^ e * (φ x / x ^ e)
      rw [hφ0 x hx, zero_div, mul_zero]
    · have hx0 : x ^ e ≠ 0 := pow_ne_zero _ (hδ.trans_le hx).ne'
      show φ x = x ^ e * (φ x / x ^ e)
      rw [mul_comm, div_mul_cancel₀ (φ x) hx0]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem ckOn_smul_of_ckOn_infinite {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hc : ContDiff ℝ ∞ c) {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (n : ℕ∞)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : _root_.Formalism.FourierDecayAlt.B.CkOn n (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => c g • F g) := by
  unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF ⊢
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hF', hEq⟩ := hF g₀ hg₀
  refine ⟨U, fun g => c g • F' g, hU, hgU, ?_, fun g hgU hg => by simp only [hEq g hgU hg]⟩
  exact (hc.contDiffOn.smul hF').of_le (WithTop.coe_le_coe.mpr le_top)

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem inCC_real_smul_comp_Gf_of_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} {A : ℝ} {m : ℕ} (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f)
    (hA : _root_.Formalism.FourierDecayAlt.B.InCC A m f) :
    _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (r : ℝ) + 2) * m) m (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k r z z' g) : ℝ) : ℂ) • f g) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
  have hcd : ContDiff ℝ ∞ (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hh.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z'))
  obtain ⟨M, hM⟩ := _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.poly_H (_root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k (0 + ρ) z z') m
  obtain ⟨K, hK0, hK⟩ := _root_.PI.UnitaryCorollaryDerivatives.CRH.main (fun g => _root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) h
    (fun _ => 2 * (0 + ρ) + 2) m M (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z') hh hb (fun w hw hne g hg => by
      have hp : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) w = (2 * (0 + ρ) + 2) * w.length := by
        simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, List.map_const', List.sum_replicate, smul_eq_mul]
        ring
      rw [hp]
      exact hM w hw hne g hg) m 0
  have hWB : _root_.PI.UnitaryCorollaryDerivatives.WB (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2))
      (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) (m + 0) K 0 := by
    unfold _root_.PI.UnitaryCorollaryDerivatives.WB
    intro u v hu hv huv g hg
    rw [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
    have hadm : _root_.PI.UnitaryCorollaryDerivatives.CRH.admitted m (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := ⟨u, v, hu, hv, huv, rfl⟩
    have hlen : (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ m := by
      simp only [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.length_append, List.length_map]; omega
    have hK1 := hK _ hadm hlen g hg
    simp only [iteratedDeriv_zero] at hK1
    have hn : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) ≤
        (List.map (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2)) (u ++ v)).sum := by
      simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.map_append, List.map_map, List.sum_append,
        List.sum_map_add, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul,
        List.length_map]
      omega
    calc _ ≤ K * _root_.Formalism.FourierDecayAlt.B.gN g ^ _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := hK1
      _ = K * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((_root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
          (by linarith [(Nat.cast_le (α := ℝ)).mpr hn])) hK0
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := _root_.PI.UnitaryCorollaryDerivatives.cC_bound (j := 0) (ρ := ρ) (E := Wq →L[ℂ] Wp) (Q := m) (o := 0)
    (mm₀ := m) (A₀ := A) hcd hWB (w := []) (fun X hX => nomatch hX) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨c, hc⟩ := id hA
  have hc' := hc
  unfold _root_.Formalism.FourierDecayAlt.B.InCC
  refine ⟨CΨ * c, ?_⟩
  unfold _root_.Formalism.FourierDecayAlt.B.CCle at hc ⊢
  refine ⟨ckOn_smul_of_ckOn_infinite hcd _ hf, fun u v hu hv huv g hg => ?_⟩
  have hIW : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k (0 + ρ)), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.unitLie k (0 + ρ) X) → _root_.Formalism.FourierDecayAlt.U.unitP k 0 ρ w :=
    fun w hw X hX => ⟨⟨(hw X hX).1, fun i b hb' _ => absurd hb' (Nat.not_lt_zero _)⟩, (hw X hX).2⟩
  have hB : ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖ ≤
      CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) :=
    hCΨ f c hc' u v (hIW u hu) (hIW v hv) huv g hg
  have hpos := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
  calc _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖
      ≤ _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        (CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A)) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hpos.le _)
    _ = CΨ * c := by
        rw [mul_comm, mul_assoc, ← Real.rpow_add hpos]
        have h0 : ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) +
            (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) = 0 := by
          simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [h0, Real.rpow_zero, mul_one]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.mulG_ckOn_inCC : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), ∀ (e m : ℕ) (φ : ℝ → ℝ)
    (f : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.GlobalTheory.HatNF.CutPow e φ →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) f → _root_.Formalism.FourierDecayAlt.B.InCC A m f →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (_root_.GlobalTheory.HatNF.mulG Bs φ f) ∧
      _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m (_root_.GlobalTheory.HatNF.mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e m φ f A hφ hf hA
  have hval : _root_.GlobalTheory.HatNF.mulG Bs φ f =
      fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g := rfl
  obtain ⟨h, hh, hb, hφh⟩ := exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow hφ
  have hφs : ContDiff ℝ ∞ φ := by
    unfold _root_.GlobalTheory.HatNF.CutPow at hφ
    exact hφ.1
  have hfun : _root_.GlobalTheory.HatNF.mulG Bs φ f = fun g =>
      ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) •
        (((h (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g) := by
    rw [hval]
    funext g
    rw [smul_smul, ← Complex.ofReal_mul, ← hφh]
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact ckOn_smul_of_ckOn_infinite (c := fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hφs.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))) ⊤ hf
  · rw [hfun]
    obtain ⟨c, hc⟩ := inCC_real_smul_comp_Gf_of_inCC Bs.z Bs.z' hh hb hf hA
    have hpd := (show (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F →
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r)
          (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g)) ∧
      ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (b : ℝ),
        _root_.Formalism.FourierDecayAlt.B.CCle (A' + (((2 * P.r + 2) * e : ℕ) : ℝ)) m' F b →
          _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g) (K * b) from
      _root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow (Wp := Wp) (Wq := Wq) Bs.z Bs.z' e).2
    obtain ⟨K, -, hK⟩ := hpd (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m
    refine ⟨K * c, hK _ c ?_⟩
    have hA' : A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m) + (((2 * P.r + 2) * e : ℕ) : ℝ) =
        A - (2 * (P.r : ℝ) + 2) * m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hA']
    exact hc

end

end GlobalTheory.HatNF
