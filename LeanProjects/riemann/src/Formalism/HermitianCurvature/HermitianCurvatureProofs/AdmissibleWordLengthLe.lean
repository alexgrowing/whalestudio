import Formalism.HermitianCurvature.HermitianCurvatureProofs.Sq2UnitOfEqOneOfSq2EqDiv

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma admissible_word_mem_lie {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : ∀ x ∈ w, inLie k r x.2 := by
  obtain ⟨u, v, hu, hv, -, rfl⟩ := h
  exact lie_LR (unit_lie hu) (unit_lie hv)

lemma admissible_word_length_le {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : w.length ≤ n := by
  obtain ⟨u, v, -, -, hl, rfl⟩ := h
  rw [len_LR]
  exact hl

section defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LSS (f : Mat k r → E) (S : Set (Mat k r)) : Prop :=
  ∀ g ∈ S, ∃ f' : Mat k r → E, ContDiff ℝ ∞ f' ∧ ∃ V : Set (Mat k r), IsOpen V ∧ g ∈ V ∧
    ∀ g' ∈ GV k r, g' ∈ V → f g' = f' g'

def UB (f : Mat k r → E) (S : Set (Mat k r)) (n : ℕ) (C : ℝ) (e γ : ℕ) : Prop :=
  ∀ w, admitted n w → ∀ g ∈ S, ‖Dw w f g‖ ≤ C * gN g ^ (e + γ * w.length)

lemma lss_of_contDiff {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) (S : Set (Mat k r)) : LSS f S := by
  intro g _
  exact ⟨f, hf, univ, isOpen_univ, mem_univ g, fun _ _ _ => rfl⟩

lemma lss_mono {f : Mat k r → E} {S S' : Set (Mat k r)} (h : LSS f S) (hS : S' ⊆ S) : LSS f S' := fun g hg => h g (hS hg)

lemma lss_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) (h : LSS f₂ S) : LSS f S := by
  intro g hg
  obtain ⟨f', hf', W, hW, hgW, hfW⟩ := h g hg
  refine ⟨f', hf', V ∩ W, hV.inter hW, ⟨hSV hg, hgW⟩, ?_⟩
  intro g' hg' hgVW
  rw [he g' hg' hgVW.1, hfW g' hg' hgVW.2]

lemma ub_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hSG : S ⊆ GV k r) (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f₂ S n C e γ) :
    UB f S n C e γ := by
  intro w hw g hg
  rw [Dw_congr_loc (admissible_word_mem_lie hw) hV he g (hSG hg) (hSV hg)]
  exact h w hw g hg

lemma lss_of_ckOn {f : Mat k r → E} {UU S : Set (Mat k r)} (hf : CkOn ⊤ UU f) (hS : S ⊆ UU) : LSS f S := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', hfU⟩ := hf g (hS hg)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU g hgU
  let χ : ContDiffBump g := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall g (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨fun x => χ x • f' x, ?_, Metric.ball g (ε / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall g (ε / 2)
    · exact χ.contDiff.contDiffAt.smul (hf'.contDiffAt (hU.mem_nhds (hcl hx)))
    · have hzero : (fun x => χ x • f' x) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        have hy' : ε / 2 ≤ dist y g := by
          simp only [mem_compl_iff, Metric.mem_closedBall, not_le] at hy
          exact hy.le
        have : χ y = 0 := χ.zero_of_le_dist hy'
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro g' hg' hgb
    have h1 : χ g' = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hgb)
    dsimp only
    rw [h1, one_smul]
    exact hfU g' (hball (Metric.ball_subset_ball (by linarith) hgb)) hg'

lemma lss_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (h : LSS f S) : LSS (fun g => L (f g)) S := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := h g hg
  exact ⟨fun x => L (f' x), L.contDiff.comp hf', V, hV, hgV,
    fun g' hg' hgV' => by dsimp only; rw [hfV g' hg' hgV']⟩

lemma ub_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (hl : LSS f S) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f S n C e γ) :
    UB (fun g => L (f g)) S n (‖L‖ * C) e γ := by
  intro w hw g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := hl g hg
  have hlie := admissible_word_mem_lie hw
  have e1 := Dw_congr_loc hlie hV (f := fun x => L (f x)) (f₂ := fun x => L (f' x))
    (fun g' hg' hgV' => by rw [hfV g' hg' hgV']) g (hSG hg) hgV
  have e2 := Dw_congr_loc hlie hV hfV g (hSG hg) hgV
  have e3 : Dw w (fun x => L (f' x)) g = L (Dw w f' g) := congrFun (dw_clm L w hf') g
  rw [e1, e3, ← e2, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h w hw g hg) (norm_nonneg L))

lemma ub_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n : ℕ} {C : ℝ} {e γ e' γ' : ℕ}
    (h : UB f S n C e γ) (hC : 0 ≤ C) (he : e ≤ e') (hγ : γ ≤ γ') : UB f S n C e' γ' := by
  intro w hw g hg
  have h1 := gN_ge_one (hSG hg)
  refine (h w hw g hg).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ h1 (Nat.add_le_add he (Nat.mul_le_mul_right _ hγ))

private lemma Dw_cons_const_eq_zero (c : E) (x : Bool × Mat k r) (w : List (Bool × Mat k r)) :
    Dw (x :: w) (fun _ : Mat k r => c) = fun _ => 0 := by
  induction w generalizing x with
  | nil =>
    funext g
    show Dx x (fun _ => c) g = 0
    rw [Dx_eq]
    exact deriv_const _ _
  | cons y w ih =>
    show Dx x (Dw (y :: w) fun _ => c) = fun _ => 0
    rw [ih]
    exact Dx_zero x

lemma ub_const (c : E) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n : ℕ) (γ : ℕ) :
    UB (fun _ : Mat k r => c) S n ‖c‖ 0 γ := by
  intro w _ g hg
  have h0 : 0 ≤ gN g := (gN_pos (hSG hg)).le
  cases w with
  | nil =>
    show ‖c‖ ≤ ‖c‖ * gN g ^ (0 + γ * 0)
    simp
  | cons x w =>
    rw [Dw_cons_const_eq_zero]
    simp only [norm_zero]
    exact mul_nonneg (norm_nonneg c) (pow_nonneg h0 _)

end defs

section app

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma leibC (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) (a : Mat k r → (F →L[ℂ] E)) (b : Mat k r → F)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hM : ∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) :
    ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  have hR : ∀ T : F →L[ℂ] E, ‖R T‖ = ‖T‖ := fun T => ContinuousLinearMap.norm_restrictScalars T
  have hRa : ContDiff ℝ ∞ (fun x => R (a x)) := R.contDiff.comp ha
  have hD : ∀ w₁ : List (Bool × Mat k r), Dw w₁ (fun x => R (a x)) g = R (Dw w₁ a g) :=
    fun w₁ => congrFun (dw_clm R w₁ ha) g
  have key := leibA g M w (fun x => R (a x)) b hRa hb
    (fun w₁ w₂ hs => by rw [hD, hR]; exact hM w₁ w₂ hs)
  exact key

lemma lss_app {S : Set (Mat k r)} {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} (ha : LSS a S) (hb : LSS b S) :
    LSS (fun g => a g (b g)) S := by
  intro g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := ha g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hb g hg
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  refine ⟨fun x => a' x (b' x), ?_, V₁ ∩ V₂, hV₁.inter hV₂, ⟨hg₁, hg₂⟩, ?_⟩
  · exact cd_app (a := fun x => R (a' x)) (R.contDiff.comp ha') hb'
  · intro g' hg' hV
    dsimp only
    rw [haV g' hg' hV.1, hbV g' hg' hV.2]

lemma ub_app {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F}
    (hla : LSS a S) (hlb : LSS b S) {n : ℕ} {Ca Cb : ℝ} {ea eb γ : ℕ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : UB a S n Ca ea γ) (hb : UB b S n Cb eb γ) :
    UB (fun g => a g (b g)) S n (2 ^ n * (Ca * Cb)) (ea + eb) γ := by
  intro w hw g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := hla g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hlb g hg
  have hgG := hSG hg
  have h0 : 0 ≤ gN g := (gN_pos hgG).le
  have hra : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' a g = Dw w' a' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₁ haV g hgG hg₁
  have hrb : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' b g = Dw w' b' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₂ hbV g hgG hg₂
  have happ : Dw w (fun x => a x (b x)) g = Dw w (fun x => a' x (b' x)) g :=
    Dw_congr_loc (admissible_word_mem_lie hw) (hV₁.inter hV₂)
      (fun g' hg' hV => by rw [haV g' hg' hV.1, hbV g' hg' hV.2]) g hgG ⟨hg₁, hg₂⟩
  have key := leibC g (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) w a' b' ha' hb' (by
    intro w₁ w₂ hs
    have hw₁ := Adm_sub hs.1 hw
    have hw₂ := Adm_sub hs.2.1 hw
    rw [← hra w₁ hw₁, ← hrb w₂ hw₂]
    have hexp : ea + γ * w₁.length + (eb + γ * w₂.length) = ea + eb + γ * w.length := by
      rw [← spl_len hs]; ring
    calc ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖
        ≤ (Ca * gN g ^ (ea + γ * w₁.length)) * (Cb * gN g ^ (eb + γ * w₂.length)) :=
          mul_le_mul (ha w₁ hw₁ g hg) (hb w₂ hw₂ g hg) (norm_nonneg _)
            (mul_nonneg hCa (pow_nonneg h0 _))
      _ = Ca * Cb * gN g ^ (ea + γ * w₁.length + (eb + γ * w₂.length)) := by rw [pow_add]; ring
      _ = Ca * Cb * gN g ^ (ea + eb + γ * w.length) := by rw [hexp])
  rw [happ]
  refine key.trans ?_
  have hM : 0 ≤ Ca * Cb * gN g ^ (ea + eb + γ * w.length) :=
    mul_nonneg (mul_nonneg hCa hCb) (pow_nonneg h0 _)
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hw)
  calc (2 : ℝ) ^ w.length * (Ca * Cb * gN g ^ (ea + eb + γ * w.length))
      ≤ 2 ^ n * (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (Ca * Cb) * gN g ^ (ea + eb + γ * w.length) := by ring

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
