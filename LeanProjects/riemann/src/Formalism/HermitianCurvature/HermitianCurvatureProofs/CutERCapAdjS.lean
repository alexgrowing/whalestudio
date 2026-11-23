import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace CAS

variable {k r : ℕ}

def TF (a : B.Mat k r → ℂ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

theorem tsupport_rdV {ψ : B.Mat k r → ℂ} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    tsupport (RdV X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hgs
  apply hg
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (Formalism.REAL.continuous_exp_real_smul X)
  have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hopen.mem_nhds
    simpa using hgs
  have hev : (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv _ 0 = 0
  rw [hev.deriv_eq]
  simp

theorem tf_rdV {a : B.Mat k r → ℂ} (ha : TF a) (X : B.Mat k r) : TF (RdV X a) := by
  exact ⟨rdV_contDiff ha.1 X, ha.2.mono' ((subset_tsupport _).trans (tsupport_rdV ha.1 X))⟩

theorem tf_rw {a : B.Mat k r → ℂ} (ha : TF a) : ∀ w : List (B.Mat k r), TF (B.Rw w a)
  | [] => ha
  | X :: w => tf_rdV (tf_rw ha w) X

theorem level_zero_set_eq_group : Q.Glev k r 0 = B.GV k r := by
  ext g
  simp only [Q.Glev, Set.mem_setOf_eq, B.GV, Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    and_true]

theorem haar0 {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) : B.IsHaarOn (Q.Glev k r 0) μ := by
  rw [level_zero_set_eq_group]
  exact h

theorem lie0 {X : B.Mat k r} (hX : B.inLie k r X) : Q.inLieLev k r 0 X := by
  exact ⟨hX, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem smooth0 {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) : Q.SmoothLev k r 0 Set.univ a := by
  exact fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial, ha.contDiffOn, fun _ _ _ => rfl⟩

theorem cpt0 {a : B.Mat k r → ℂ} (ha : HasCompactSupport a) : Q.CptOn k r 0 a := by
  exact ⟨tsupport a, ha, fun g _ hg => image_eq_zero_of_notMem_tsupport hg⟩

theorem word_adj_scalar {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) :
    ∀ (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) → ∀ {a b : B.Mat k r → ℂ}, TF a → TF b →
      (∫ x : Mt k r, B.Rw w a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
        (-1 : ℂ) ^ w.length * ∫ x : Mt k r, a (Matrix.of x) * star (B.Rw w.reverse b (Matrix.of x)) ∂μ
  | [], _, a, b, _, _ => by simp [B.Rw]
  | X :: w, hw, a, b, ha, hb => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have e1 : B.Rw (X :: w) a = RdV X (B.Rw w a) := rfl
    have e2 : B.Rw (X :: w).reverse b = B.Rw w.reverse (RdV X b) := by
      simp only [B.Rw, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hra := tf_rw ha w
    have sk := Formalism.FourierDecayAlt.P.right_differential_skew k r 0 μ (haar0 h) X (B.Rw w a) b (lie0 hX) (smooth0 hra.1)
      (smooth0 hb.1) (cpt0 hra.2) (cpt0 hb.2)
    rw [e1, sk, word_adj_scalar h w hw' ha (tf_rdV hb X), e2, List.length_cons, pow_succ]
    ring

end CAS

open CAS in
theorem capacity_adjoint_scalar : CapAdjScalar := by
  intro k r Y μ h a b ha hac hb hbc
  have ta : TF a := ⟨ha, hac⟩
  have tb : TF b := ⟨hb, hbc⟩
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw hc X hX => ((hLw cw hc).1 X hX).1

  have hintA : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      ha.continuous.mul (continuous_star.comp hv)
    have hs : HasCompactSupport (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      hac.mono fun x hx h0 => hx (by show a x * _ = 0; rw [h0, zero_mul])
    exact hc.integrable_of_hasCompactSupport hs
  have hintB : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hv.mul (continuous_star.comp hb.continuous)
    have hs : HasCompactSupport (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hbc.mono fun x hx h0 => hx (by show _ * star (b x) = 0; rw [h0, star_zero, mul_zero])
    exact hc.integrable_of_hasCompactSupport hs

  have hH := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r 0 0 0 μ (haar0 h) (fun _ _ => rfl) (fun _ _ => rfl) a b
    (smooth0 ha) (smooth0 hb) (cpt0 hac) (cpt0 hbc) Y 0 0
  have eT : ∀ (Y' : ℂ), Q.tL k r (E := ℂ) 0 0 0 Y' 0 0 = Q.CV k r Y' := fun _ => rfl
  have eS : star Y = conj Y := rfl
  rw [eT, eT, eS] at hH
  rw [← hH]

  have e2 : (∫ x : Mt k r, Q.CV k r Y a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * (B.Rw cw.2 a (Matrix.of x) * star (b (Matrix.of x)))).sum ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae h] with x hx
    have := hCV ℂ (B.GV k r) a (ckOn_of_contDiff ha _ _) (Matrix.of x) hx hx
    rw [this, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    rw [smul_eq_mul, mul_assoc]

  have e1 : (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * ((-1 : ℂ) ^ cw.2.length * (a (Matrix.of x) * star (B.Rw cw.2.reverse b (Matrix.of x))))).sum ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [wsAdj, Complex.star_def, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    simp only [Function.comp_apply, map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
    ring
  rw [e1, e2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ =>
      ((hintA _ (tf_rw tb _).1.continuous).const_mul _).const_mul _).2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ => (hintB _ (tf_rw ta _).1.continuous).const_mul _).2]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    word_adj_scalar h cw.2 (hLie cw hcw) ta tb]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
