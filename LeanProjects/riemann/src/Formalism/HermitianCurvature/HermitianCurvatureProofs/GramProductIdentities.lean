import Formalism.HermitianCurvature.PositionExpansionTopCoefficients
import Lemmata.HermitianSesquilinear.ConjEqOfNonnegReal

namespace Formalism.FourierDecayAlt.P.GramProductIdentities

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem act_add (M : SlopeTestRemainingChoices S A) (X Y : Ix S → V) : act M (X + Y) = act M X + act M Y := by
  funext z; simp [act, smul_add, Finset.sum_add_distrib]

theorem act_smul (M : SlopeTestRemainingChoices S A) (c : ℂ) (X : Ix S → V) : act M (c • X) = c • act M X := by
  funext z
  simp only [act, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun z' _ => (smul_comm c (M z z') (X z')).symm

theorem act_mul (M N : SlopeTestRemainingChoices S A) (X : Ix S → V) : act (M * N) X = act M (act N X) := by
  funext z
  simp only [act, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem act_one (X : Ix S → V) : act (1 : SlopeTestRemainingChoices S A) X = X := by
  funext z; simp [act, Matrix.one_apply, ite_smul]

theorem act_csmul (M : SlopeTestRemainingChoices S A) (c : ℂ) (X : Ix S → V) : act (c • M) X = c • act M X := by
  funext z; simp only [act, Matrix.smul_apply, smul_assoc, Pi.smul_apply, Finset.smul_sum]

theorem pair_act (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) :
    pair ρ (act M X) X' = pair ρ X (act (star M) X') := by
  simp only [pair, act, map_sum, LinearMap.sum_apply, ρ.adj, Matrix.star_apply]
  exact Finset.sum_comm

theorem pair_act' (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) :
    pair ρ X (act M X') = pair ρ (act (star M) X) X' := by
  rw [pair_act, star_star]

def frmS (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) : F7.Sesq (Ix S → V) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun X X' => frm ρ M X X')
    (fun X Y Z => by simp [frm, pair, act_add, map_add, Finset.sum_add_distrib])
    (fun c X Z => by simp [frm, pair, act_smul, Finset.mul_sum])
    (fun X Y Z => by simp [frm, pair, map_add, Finset.sum_add_distrib])
    (fun c X Z => by simp [frm, pair, Finset.mul_sum])

theorem frmS_apply (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) : frmS ρ M X X' = frm ρ M X X' := rfl

end Rep

section CS

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem cs_of_pos (Ξ : F7.Sesq M) (h : ∀ m, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    ‖Ξ x y‖ ^ 2 ≤ (Ξ x x).re * (Ξ y y).re := by
  first | exact Bl.HermitianSesquilinear.goal1 .. | (apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (intros; apply @Bl.HermitianSesquilinear.goal1 <;> assumption) | (apply @Bl.HermitianSesquilinear.goal1 <;> first | assumption | infer_instance) | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x y | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h x | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ h | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› Ξ | exact @Bl.HermitianSesquilinear.goal1 M ‹_› ‹_› | exact @Bl.HermitianSesquilinear.goal1 M ‹_› | exact @Bl.HermitianSesquilinear.goal1 M

end CS

theorem pairAdj : PairAdj := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ M N c X X'
  exact ⟨act_mul M N X, act_one X, act_csmul M c X, pair_act ρ M X X'⟩

theorem csPos : CSPos := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ M X X' hP
  have := cs_of_pos (frmS ρ M) (fun m => hP m) X X'
  simpa [frmS_apply] using this

theorem formSesq : FormSesq := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ M
  exact ⟨frmS ρ M, fun _ _ => rfl⟩

theorem p1aBound : CauchySchwarzInvariantForm := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ RR W x hP hW
  have hcs := csPos A S V ρ RR (act W x) x hP
  have hWW : frm ρ RR (act W x) (act W x) = frm ρ RR x x := by
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hW]
  rw [hWW] at hcs
  have h0 := (hP x).1
  nlinarith [norm_nonneg (frm ρ RR (act W x) x)]

theorem gramSum : GramSum := by
  intro M _ _ R ι _ d io X X'
  symm
  calc ∑ k, R (∑ h, io h k • X h) (∑ h, io h k • X' h)
      = ∑ k, ∑ h, ∑ h', io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ∀ (u : M), R (∑ h, io h k • X h) u = ∑ h, io h k * R (X h) u := by
          intro u; rw [map_sum R, LinearMap.sum_apply]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        have e2 : ∀ (u : M), R u (∑ h', io h' k • X' h') =
            ∑ h', starRingEnd ℂ (io h' k) * R u (X' h') := by
          intro u; rw [map_sum (R u)]; simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
        rw [e1]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [e2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h' _ => ?_
        ring
    _ = ∑ h, ∑ k, ∑ h', io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') := Finset.sum_comm
    _ = ∑ h, ∑ h', ∑ k, io h k * starRingEnd ℂ (io h' k) * R (X h) (X' h') :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]

theorem gramPos : GramPos := by
  intro M _ _ R d h x
  constructor
  · rw [Complex.re_sum]; exact Finset.sum_nonneg fun k _ => (h _).1
  · rw [Complex.im_sum]; exact Finset.sum_eq_zero fun k _ => (h _).2

theorem gramRealise : GramRealise := by
  intro ι _ _ kap hk
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hk.nonneg
  refine ⟨Fintype.card ι, fun h k => star (B ((Fintype.equivFin ι).symm k) h), fun h h' => ?_⟩
  rw [hB, Matrix.mul_apply]
  refine Fintype.sum_equiv (Fintype.equivFin ι) _ _ fun i => ?_
  show star B h i * B i h' = star (B ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)) h) *
    starRingEnd ℂ (star (B ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)) h'))
  rw [Equiv.symm_apply_apply, Matrix.star_apply, starRingEnd_apply, star_star]

theorem exp_le_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp (-2 * |x|) ≤ 1 + x := by
  rcases le_or_gt 0 x with h0 | h0
  · have : Real.exp (-2 * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
    linarith
  · have hu : |x| = -x := abs_of_neg h0
    set u := -x with hu'
    have hu0 : 0 ≤ u := by linarith
    have hu1 : u ≤ 1 / 2 := by rw [← hu]; exact hx
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have h2 : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (-2 * u) * (1 + 2 * u) ≤ 1 := by
      calc Real.exp (-2 * u) * (1 + 2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    rw [hu]
    have he := Real.exp_pos (-2 * u)
    nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ 1 - 2 * u)]

theorem logSmall : LogSmall := by
  intro x hx
  have hpos : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  rw [abs_le]
  constructor
  · have h := exp_le_one_add hx
    have := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    have := le_abs_self x
    have := abs_nonneg x
    linarith

theorem prod_bounds {ι : Type} (g : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2) :
    ∀ w : List ι, (∀ l ∈ w, |g l - 1| ≤ ε) →
      Real.exp (-2 * ε * w.length) ≤ (w.map g).prod ∧ (w.map g).prod ≤ Real.exp (ε * w.length) := by
  intro w
  induction w with
  | nil => intro _; simp
  | cons l w ih =>
    intro hw
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hw l' (by simp [hl'])
    have hl := hw l (by simp)
    have hx : |g l - 1| ≤ 1 / 2 := le_trans hl hε
    have hlo : Real.exp (-2 * ε) ≤ g l := by
      have := exp_le_one_add hx
      have : Real.exp (-2 * ε) ≤ Real.exp (-2 * |g l - 1|) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hhi : g l ≤ Real.exp ε := by
      have := Real.add_one_le_exp (g l - 1)
      have : Real.exp (g l - 1) ≤ Real.exp ε := Real.exp_le_exp.mpr (le_trans (le_abs_self _) hl)
      linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have e1 : Real.exp (-2 * ε * (w.length + 1)) = Real.exp (-2 * ε) * Real.exp (-2 * ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (ε * (w.length + 1)) = Real.exp ε * Real.exp (ε * w.length) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    constructor
    · exact mul_le_mul hlo ih1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hlo)
    · exact mul_le_mul hhi ih2 (le_trans (Real.exp_pos _).le ih1) (Real.exp_pos _).le

theorem qProduct : QProduct := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil => simp [qw, hq]
  | cons l w ih =>
    have hl := hw l (by simp)
    have ih' := ih fun l' hl' => hw l' (by simp [hl'])
    simp only [qw, List.map_cons, List.prod_cons]
    rw [← ih']
    cases hp : l.plus
    · simp only [hp] at hl ⊢
      simp only [Bool.false_eq_true, if_false]
      have h2 : l.pt - Y - 1 ≠ 0 := hl
      field_simp
      try ring
    · simp only [hp] at hl ⊢
      simp only [if_true]
      have h2 : Y - l.pt ≠ 0 := hl
      field_simp
      try ring

theorem lemmaQ : LemmaQ := by
  intro S _ _ q w N dl Y hN hw hdl hpts hq
  have hN' : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hdlpos : 0 < dl := by nlinarith
  set g : Letter ℝ S → ℝ := fun l => if l.plus then 1 + 1 / (Y - l.pt) else 1 + 1 / (l.pt - Y - 1)
    with hg
  have hfac : ∀ l ∈ w, |g l - 1| ≤ 1 / dl := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h
      simp only [hg, hp, Bool.false_eq_true, if_false, add_sub_cancel_left, abs_div, abs_one]
      have : |l.pt - Y - 1| = |Y - (l.pt - 1)| := by rw [← abs_neg]; ring_nf
      rw [this]
      exact one_div_le_one_div_of_le hdlpos h.2
    · simp only [hp, if_true] at h
      simp only [hg, hp, if_true, add_sub_cancel_left, abs_div, abs_one]
      exact one_div_le_one_div_of_le hdlpos h
  have hreg : ∀ l ∈ w, if l.plus then Y - l.pt ≠ 0 else l.pt - Y - 1 ≠ 0 := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
      intro h0
      have : |Y - (l.pt - 1)| = 0 := by rw [abs_eq_zero]; linarith
      linarith [h.2]
    · simp only [hp, if_true] at h ⊢
      intro h0
      rw [h0, abs_zero] at h
      linarith
  have hprod := qProduct S q w Y hq hreg
  have hε : 1 / dl ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  obtain ⟨hlo, hhi⟩ := prod_bounds g (1 / dl) hε w hfac
  have hlen : (w.length : ℝ) ≤ N := by exact_mod_cast hw
  have hkey : 1 / dl * w.length ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdlpos]
    nlinarith
  rw [hprod]
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) hlo
    nlinarith
  · refine le_trans hhi (Real.exp_le_exp.mpr ?_)
    linarith

theorem lemmaQOfParts : LemmaQOfParts := fun _ _ => lemmaQ

theorem gridSpacing : GridSpacing := by
  intro α β N hab hN
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hI : 0 < β - α := by linarith
  have hL : 0 < (β - α) / (6 * N) := by positivity
  have h2NL : 2 * (N:ℝ) * ((β - α) / (6 * N)) = (β - α) / 3 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have e : (β - α) / (6 * N) - (β - α) / (7 * N) = (β - α) / (42 * N) := by field_simp; ring
    have : 1 ≤ (β - α) / (42 * N) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · intro a ha y h1 h2
    rw [Finset.mem_Icc] at ha
    have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha.1
    have ha2 : (a:ℝ) ≤ N := by exact_mod_cast ha.2
    unfold gl at h1 h2
    have : (2 * (a:ℝ) - 2) * ((β - α) / (6 * N)) ≥ 0 := mul_nonneg (by linarith) hL.le
    have : (2 * (a:ℝ) - 1) * ((β - α) / (6 * N)) ≤ 2 * N * ((β - α) / (6 * N)) :=
      mul_le_mul_of_nonneg_right (by linarith) hL.le
    constructor
    · linarith
    · nlinarith
  · intro a ha b hb hab' y y' h1 h2 h3 h4 e he e' he'
    rw [Finset.mem_Icc] at ha hb
    unfold gl at h1 h2 h3 h4
    have he2 : 0 ≤ e ∧ e ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> norm_num
    have he2' : 0 ≤ e' ∧ e' ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at he'
      rcases he' with rfl | rfl <;> norm_num
    rcases Nat.lt_or_gt_of_ne hab' with hlt | hlt
    · have hc : (a:ℝ) + 1 ≤ b := by exact_mod_cast hlt
      have : 2 * ((b:ℝ) - a) * ((β - α) / (6 * N)) ≥ 2 * ((β - α) / (6 * N)) := by
        nlinarith
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      nlinarith
    · have hc : (b:ℝ) + 1 ≤ a := by exact_mod_cast hlt
      have : 2 * ((a:ℝ) - b) * ((β - α) / (6 * N)) ≥ 2 * ((β - α) / (6 * N)) := by
        nlinarith
      refine le_trans ?_ (le_abs_self _)
      nlinarith
  · intro h
    rw [le_div_iff₀ (by positivity)]
    nlinarith

theorem dkStep4 : DKStep4 := by
  intro S q w L hL
  induction L with
  | nil => simp [kapF]
  | cons l L ih =>
    have hl : l.plus = true := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true := fun l' h => hL l' (by simp [h])
    have h1 : (L.map fun l' => if l.plus = l'.plus then (1:ℂ)
        else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨l', hl', rfl⟩ := hx
      simp [hl, hL' l' hl']
    simp only [kapF, List.map_cons, List.prod_cons]
    rw [h1, ih hL']
    simp only [ypt, hl, if_true]
    ring

end Formalism.FourierDecayAlt.P.GramProductIdentities

theorem Formalism.FourierDecayAlt.P.pairing_adjoint_identity : Formalism.FourierDecayAlt.FormPairingAction.PairAdj := Formalism.FourierDecayAlt.P.GramProductIdentities.pairAdj
theorem Formalism.FourierDecayAlt.P.cauchy_schwarz_positive : Formalism.FourierDecayAlt.FormPairingAction.CSPos := Formalism.FourierDecayAlt.P.GramProductIdentities.csPos
theorem Formalism.FourierDecayAlt.P.form_sesquilinear : Formalism.FourierDecayAlt.FormPairingAction.FormSesq := Formalism.FourierDecayAlt.P.GramProductIdentities.formSesq
theorem Formalism.FourierDecayAlt.P.gram_sum_identity : Formalism.FourierDecayAlt.FormPairingAction.GramSum := Formalism.FourierDecayAlt.P.GramProductIdentities.gramSum
theorem Formalism.FourierDecayAlt.P.gram_matrix_positive : Formalism.FourierDecayAlt.FormPairingAction.GramPos := Formalism.FourierDecayAlt.P.GramProductIdentities.gramPos
theorem Formalism.FourierDecayAlt.P.gram_matrix_realisation : Formalism.FourierDecayAlt.FormPairingAction.GramRealise := Formalism.FourierDecayAlt.P.GramProductIdentities.gramRealise
theorem Formalism.FourierDecayAlt.P.first_polynomial_bound : Formalism.FourierDecayAlt.FormPairingAction.CauchySchwarzInvariantForm := Formalism.FourierDecayAlt.P.GramProductIdentities.p1aBound
theorem Formalism.FourierDecayAlt.P.logarithm_small_estimate : Formalism.FourierDecayAlt.FormPairingAction.LogSmall := Formalism.FourierDecayAlt.P.GramProductIdentities.logSmall
theorem Formalism.FourierDecayAlt.P.Q_product_identity : Formalism.FourierDecayAlt.FormPairingAction.QProduct := Formalism.FourierDecayAlt.P.GramProductIdentities.qProduct
theorem Formalism.FourierDecayAlt.P.lemma_Q_estimate : Formalism.FourierDecayAlt.FormPairingAction.LemmaQ := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQ
theorem Formalism.FourierDecayAlt.P.lemma_Q_of_parts : Formalism.FourierDecayAlt.FormPairingAction.LemmaQOfParts := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQOfParts
theorem Formalism.FourierDecayAlt.P.grid_spacing_estimate : Formalism.FourierDecayAlt.FormPairingAction.GridSpacing := Formalism.FourierDecayAlt.P.GramProductIdentities.gridSpacing
theorem Formalism.FourierDecayAlt.P.fourth_reduction_estimate : Formalism.FourierDecayAlt.FormPairingAction.DKStep4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4
