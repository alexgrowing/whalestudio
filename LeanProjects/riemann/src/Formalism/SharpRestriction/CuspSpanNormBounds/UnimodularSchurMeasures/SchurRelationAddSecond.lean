import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section Q

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ)

def pj_Q (x y x' y' : Hs) : Prop :=
  Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ ∧
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y'⟫_ℂ / (d : ℂ)

variable {μ σ d}

theorem pj_Q_zero1 (y x' y' : Hs) : pj_Q μ σ d 0 y x' y' := by
  unfold pj_Q
  simp

theorem schur_relation_add_first {x1 x2 y x' y' : Hs} (h1 : pj_Q μ σ d x1 y x' y') (h2 : pj_Q μ σ d x2 y x' y') :
    pj_Q μ σ d (x1 + x2) y x' y' := by
  have e : (fun g => ⟪y, σ g (x1 + x2)⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => ⟪y, σ g x1⟫_ℂ * star ⟪y', σ g x'⟫_ℂ + ⟪y, σ g x2⟫_ℂ * star ⟪y', σ g x'⟫_ℂ := by
    funext g
    rw [map_add, inner_add_right, add_mul]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.add h2.1, ?_⟩
  rw [integral_add h1.1 h2.1, h1.2, h2.2, inner_add_right]
  ring

theorem pj_Q_smul1 {x y x' y' : Hs} (a : ℂ) (h1 : pj_Q μ σ d x y x' y') : pj_Q μ σ d (a • x) y x' y' := by
  have e : (fun g => ⟪y, σ g (a • x)⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => a * (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [map_smul, inner_smul_right, mul_assoc]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.const_mul a, ?_⟩
  rw [integral_const_mul, h1.2, inner_smul_right]
  ring

theorem pj_Q_zero2 (x x' y' : Hs) : pj_Q μ σ d x 0 x' y' := by
  unfold pj_Q
  simp

theorem schur_relation_add_second {x y1 y2 x' y' : Hs} (h1 : pj_Q μ σ d x y1 x' y') (h2 : pj_Q μ σ d x y2 x' y') :
    pj_Q μ σ d x (y1 + y2) x' y' := by
  have e : (fun g => ⟪y1 + y2, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => ⟪y1, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ + ⟪y2, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ := by
    funext g
    rw [inner_add_left, add_mul]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.add h2.1, ?_⟩
  rw [integral_add h1.1 h2.1, h1.2, h2.2, inner_add_left]
  ring

theorem pj_Q_smul2 {x y x' y' : Hs} (a : ℂ) (h1 : pj_Q μ σ d x y x' y') : pj_Q μ σ d x (a • y) x' y' := by
  have e : (fun g => ⟪a • y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => (starRingEnd ℂ) a * (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [inner_smul_left, mul_assoc]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.const_mul _, ?_⟩
  rw [integral_const_mul, h1.2, inner_smul_left]
  ring

theorem pj_Q_symm {x y x' y' : Hs} (h : pj_Q μ σ d x y x' y') : pj_Q μ σ d x' y' x y := by
  have e : (fun g => ⟪y', σ g x'⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => (starRingEnd ℂ) (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [map_mul, ← starRingEnd_apply, ← starRingEnd_apply, Complex.conj_conj, mul_comm]
  unfold pj_Q
  rw [e]
  refine ⟨(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h.1, ?_⟩
  rw [integral_conj, h.2, map_div₀, map_mul, inner_conj_symm, inner_conj_symm, Complex.conj_ofReal]

theorem schur_relation_span {S : Set Hs} {x' y' : Hs} (hS : ∀ a ∈ S, ∀ b ∈ S, pj_Q μ σ d a b x' y') :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ S, pj_Q μ σ d x y x' y' := by
  have h1 : ∀ x ∈ Submodule.span ℂ S, ∀ b ∈ S, pj_Q μ σ d x b x' y' := by
    intro x hx b hb
    induction hx using Submodule.span_induction with
    | mem a ha => exact hS a ha b hb
    | zero => exact pj_Q_zero1 _ _ _
    | add u v _ _ hu hv => exact schur_relation_add_first hu hv
    | smul a u _ hu => exact pj_Q_smul1 a hu
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem b hb => exact h1 x hx b hb
  | zero => exact pj_Q_zero2 _ _ _
  | add u v _ _ hu hv => exact schur_relation_add_second hu hv
  | smul a u _ hu => exact pj_Q_smul2 a hu

theorem pj_Q_span {S : Set Hs} (hS : ∀ a ∈ S, ∀ b ∈ S, ∀ a' ∈ S, ∀ b' ∈ S, pj_Q μ σ d a b a' b') :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ S, ∀ x' ∈ Submodule.span ℂ S, ∀ y' ∈ Submodule.span ℂ S,
      pj_Q μ σ d x y x' y' := by
  intro x hx y hy
  refine fun x' hx' y' hy' => pj_Q_symm ?_
  refine schur_relation_span (fun a' ha' b' hb' => pj_Q_symm ?_) x' hx' y' hy'
  exact schur_relation_span (fun a ha b hb => hS a ha b hb a' ha' b' hb') x hx y hy

theorem pj_Q_diag {x y : Hs} (h : pj_Q μ σ d x y x y) :
    Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := h
  have hfun : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) = fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
  rw [integral_complex_ofReal] at he
  have h2 : ((∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  exact_mod_cast h2

end Q

theorem pj_Q_pure (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (a b a' b' : ∀ v, X.H v) :
    pj_Q (muInf X) X.σs (fdegAll X.I X.σ X.w) (X.tens a) (X.tens b) (X.tens a') (X.tens b') := by
  have hd : ∀ v, IsFdeg (Formalism.REAL.muG (X.I.ε v)) (X.σ v) (fdegOf (Formalism.REAL.muG (X.I.ε v)) (X.σ v) (X.w v)) := by
    intro v
    obtain ⟨d, hd⟩ := h1 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)
    rw [fdegOf_eq hd (hX.2.1.2.1 v).1]
    exact hd
  have hc : ∀ (a b : ∀ v, X.H v) (g : X.I.Ginf),
      ⟪X.tens b, X.σs g (X.tens a)⟫_ℂ = ∏ v, coefOn (X.σ v) (a v) (b v) (g v) := by
    intro a b g
    rw [hX.2.1.2.2.1.2.1 g a, hX.2.1.2.2.1.1]
    rfl
  have e : (fun g => ⟪X.tens b, X.σs g (X.tens a)⟫_ℂ * star ⟪X.tens b', X.σs g (X.tens a')⟫_ℂ) =
      fun g : X.I.Ginf => ∏ v, (fun y => coefOn (X.σ v) (a v) (b v) y * star (coefOn (X.σ v) (a' v) (b' v) y)) (g v) := by
    funext g
    rw [hc, hc, Finset.prod_mul_distrib]
    congr 1
    exact map_prod (starRingEnd ℂ) _ _
  unfold pj_Q
  rw [e]
  refine ⟨Integrable.fintype_prod_dep fun v => ((hd v).2 (a v) (b v) (a' v) (b' v)).1, ?_⟩
  refine (integral_fintype_prod_eq_prod (μ := fun v => Formalism.REAL.muG (X.I.ε v))
    (fun v y => coefOn (X.σ v) (a v) (b v) y * star (coefOn (X.σ v) (a' v) (b' v) y))).trans ?_
  simp only [((hd _).2 _ _ _ _).2]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hX.2.1.2.2.1.1, hX.2.1.2.2.1.1]
  unfold fdegAll
  push_cast
  rfl

theorem pj_schur_span (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) :
    ∀ x ∈ Submodule.span ℂ (Set.range X.tens), ∀ y ∈ Submodule.span ℂ (Set.range X.tens),
      Integrable (fun g => ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2) (muInf X) ∧
        ∫ g, ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2 ∂(muInf X) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdegAll X.I X.σ X.w := by
  intro x hx y hy
  refine pj_Q_diag (pj_Q_span ?_ x hx y hy x hx y hy)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
  exact pj_Q_pure D h1 X hX a b a' b'

end Formalism.MainNotions.LeviCoordinates

end
