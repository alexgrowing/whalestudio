import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma one_le_gN {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := (Formalism.FourierDecayAlt.P.norm_of_inverse k r g hg).2

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (one_le_gN hg)

lemma rpow_mono_G {g : Mat k r} (hg : g ∈ GV k r) {a b : ℝ} (h : a ≤ b) : gN g ^ a ≤ gN g ^ b :=
  Real.rpow_le_rpow_of_exponent_le (one_le_gN hg) h

lemma loss_bound_nonneg (r : ℕ) : 0 ≤ C2.B0 r := by unfold C2.B0; positivity

lemma top_ge_nat (m : ℕ) : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

lemma ckOn_top_nat {f : Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) (m : ℕ) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (top_ge_nat m), hff⟩

lemma top_ne_zero' : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp

lemma top_succ_le : (((⊤ : ℕ∞)) : WithTop ℕ∞) + 1 ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ⊤)

lemma ckOn_op_top {f : Mat k r → E} {X : Mat k r} (b : Bool) (hf : CkOn (⊤ : ℕ∞) (GV k r) f)
    (hX : inLie k r X) : CkOn (⊤ : ℕ∞) (GV k r) (op b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, op' b X f', hU, hgU, ?_, ?_⟩
  · exact (hc.fderiv_of_isOpen hU top_succ_le).clm_apply (vf b X).contDiff.contDiffOn
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hc.differentiableOn top_ne_zero').differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma ckOn_W_top {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn (⊤ : ℕ∞) (GV k r) f) : CkOn (⊤ : ℕ∞) (GV k r) (W w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [W_cons]
    exact ckOn_op_top x.1 (ih fun y hy => hw y (List.mem_cons_of_mem _ hy)) (hw x List.mem_cons_self)

lemma right_word_eq_word (v : List (Mat k r)) (f : Mat k r → E) : Rw v f = W (lr [] v) f := by
  rw [← dLR_eq]; rfl

lemma foldr_LdV_eq_W_lr (u : List (Mat k r)) (f : Mat k r → E) : u.foldr LdV f = W (lr u []) f := by
  rw [← dLR_eq]; rfl

lemma allLie_lr' {u v : List (Mat k r)} (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, inLie k r X) :
    AllLie (lr u v) := by
  intro x hx
  simp only [lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

lemma L_Rw_comm {X : Mat k r} (hX : inLie k r X) : ∀ (v : List (Mat k r)), (∀ Y ∈ v, inLie k r Y) →
    ∀ K : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      Rw v (LdV X K) g = LdV X (Rw v K) g := by
  intro v
  induction v with
  | nil => intro _ K _ g _; rfl
  | cons Y v ih =>
    intro hv K hK g hg
    have hv' : ∀ Z ∈ v, inLie k r Z := fun Z hZ => hv Z (List.mem_cons_of_mem _ hZ)
    have hY := hv Y List.mem_cons_self
    show op false Y (Rw v (LdV X K)) g = op true X (op false Y (Rw v K)) g
    rw [op_congr false hY (ih hv' K hK) g hg]
    have hc : CkOn (⊤ : ℕ∞) (GV k r) (Rw v K) := by
      rw [right_word_eq_word]; exact ckOn_W_top _ (allLie_lr' (by simp) hv') hK
    exact op_comm (ckOn_top_nat hc 2) hX hY hg

lemma dLR_R (u v : List (Mat k r)) (X : Mat k r) (F : Mat k r → E) :
    dLR u v (RdV X F) = dLR u (v ++ [X]) F := by
  unfold dLR Rw; rw [List.foldr_append]; rfl

lemma dLR_L {u v : List (Mat k r)} {X : Mat k r} (hu : ∀ Y ∈ u, inLie k r Y) (hv : ∀ Y ∈ v, inLie k r Y)
    (hX : inLie k r X) {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, dLR u v (LdV X F) g = dLR (u ++ [X]) v F g := by
  intro g hg
  have e1 : dLR u v (LdV X F) = W (lr u []) (Rw v (LdV X F)) := by
    rw [← foldr_LdV_eq_W_lr]; rfl
  have e2 : dLR (u ++ [X]) v F = W (lr u []) (LdV X (Rw v F)) := by
    rw [← foldr_LdV_eq_W_lr]; unfold dLR; rw [List.foldr_append]; rfl
  rw [e1, e2]
  exact W_congr _ (allLie_lr' hu (by simp)) (L_Rw_comm hX v hv F hF) g hg

lemma chart_rho {g0 x : Mat k r} (hg0 : g0 ∈ GV k r) (hx : x ∈ Sr g0) (hxG : x ∈ GV k r) :
    chart g0 (rho g0 x) = x := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
  obtain ⟨hl, -, hk⟩ := iot_facts hh hx
  show kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0 = x
  rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

lemma rho_self {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : rho g0 g0 = 0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  funext i
  simp only [Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
  exact co_zero i

lemma self_mem_Sr {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _

lemma chart_comp_cd {F : Mat k r → E} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (m : ℕ)
    (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨U, f', hU, hcU, hcd, hff⟩ := hF _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y' => f' (chart g0 Y')) Y :=
    (hcd.contDiffAt (hU.mem_nhds hcU)).comp Y
      (((chart_cd g0).contDiffAt (dom_open.mem_nhds hY)).of_le (top_ge_nat m))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact hff _ h1 (chart_mem hg0 h2)

theorem ckOn_top_of_all {F : Mat k r → E} (hF : ∀ m : ℕ, CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) F := by
  intro g0 hg0
  have hAL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) :=
    contDiffOn_infty.2 fun m => chart_comp_cd hg0 m (hF m)
  set U := Sr g0 ∩ rho g0 ⁻¹' Dom k r with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) dom_open
  have hg0U : g0 ∈ U := ⟨self_mem_Sr hg0, by show rho g0 g0 ∈ Dom k r; rw [rho_self hg0]; exact zero_mem_dom⟩
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · exact hAL.comp ((rho_cd g0).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    show F x = F (chart g0 (rho g0 x))
    rw [chart_rho hg0 hx.1 hxG]

theorem rule_A1_derivatives : C2.FiniteOrderIntersectionInSmooth := by
  intro k r E _ _ A F hF
  refine ⟨ckOn_top_of_all fun m => (hF m).choose_spec.1, ?_⟩
  intro u v hu hv
  obtain ⟨c, hc⟩ := hF (u.length + v.length)
  refine ⟨c, fun g hg => le_trans ?_ (hc.2 u v hu hv le_rfl g hg)⟩
  refine mul_le_mul_of_nonneg_right (rpow_mono_G hg ?_) (norm_nonneg _)
  have : 0 ≤ C2.B0 r * ((u.length : ℝ) + v.length) := mul_nonneg (loss_bound_nonneg r) (by positivity)
  linarith

theorem ruleB : C2.RuleB := by
  intro k r E _ _ A F hF X hX
  refine ⟨⟨ckOn_op_top false hF.1 hX.1, ?_⟩, ⟨ckOn_op_top true hF.1 hX.1, ?_⟩⟩
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 u (v ++ [X]) hu (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hv Y h
      · rw [List.mem_singleton.1 h]; exact hX)
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * ((u.length : ℝ) + (v ++ [X]).length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_R] at this
    exact this
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 (u ++ [X]) v (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hu Y h
      · rw [List.mem_singleton.1 h]; exact hX) hv
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * (((u ++ [X]).length : ℝ) + v.length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_L (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) hX.1 hF.1 g hg] at this
    exact this

end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

namespace Formalism.FourierDecayAlt.P

theorem rule_A1_of_derivatives : C2.FiniteOrderIntersectionInSmooth := SmoothnessOrderArithmetic.rule_A1_derivatives

theorem rule_B_derivatives : C2.RuleB := SmoothnessOrderArithmetic.ruleB

end Formalism.FourierDecayAlt.P
