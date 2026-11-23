import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma fc_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (N : ℕ) :
    CkOn N (GV k r) (C6.cutAll D χ₀ de L F) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted N W → ∀ g ∈ GV k r,
      ‖Dw W (C6.cutAll D χ₀ de L F) g‖ ≤ C * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) := by
  obtain ⟨⟨Cχ, hCχ0, hCχ⟩, hlχ⟩ := ubl_chi D hχ de L N
  set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ
  set a : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)
  have hGG : GV k r ⊆ GV k r := le_rfl
  have hua := ub_clm Lid hGG hlχ hCχ
  have hla := lss_clm Lid hlχ
  obtain ⟨c, hc⟩ := hF N
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hP : Pr (∅ : Set (Mat k r)) (GV k r) N a F :=
    ⟨sCkOn_mono le_top (ckOn_of_lss hla ⊤), hc.1, fun _ _ h => absurd h (notMem_empty _)⟩
  have eq : C6.cutAll D χ₀ de L F = ap a F := by
    funext g; simp [C6.cutAll, ap, a, Lid]
  rw [eq]
  refine ⟨hP.ck isOpen_empty hcov, 2 ^ N * (‖Lid‖ * Cχ * max c 0), by positivity, fun W hW g hg => ?_⟩
  have hgp := gN_pos hg
  have hg1 := gN_ge_one hg
  set M := ‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) with hM
  have hb := leib_bound isOpen_empty hcov g hg M W a F (admissible_word_mem_lie hW)
    (hP.mono (by exact_mod_cast admissible_word_length_le hW)) (by
      intro w₁ w₂ h₁ h₂ hl
      have b1 := hua w₁ (Adm_sub h₁ hW) g hg
      have b2 : ‖Dw w₂ F g‖ ≤ max c 0 * gN g ^ (-A₀) := by
        obtain ⟨u, v, hu, hv, hl', hw2⟩ := Adm_sub h₂ hW
        rw [hw2, ← dLR_eq]
        have := hc.2 u v hu hv hl' g hg
        rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgp _), mul_comm]
        exact this.trans (le_max_left _ _)
      have hex : (((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀) ≤ -A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ) := by
        have : (2 * r + 2) * w₁.length ≤ (2 * r + 2) * W.length :=
          Nat.mul_le_mul_left _ (by omega)
        have : (((2 * r + 2) * w₁.length : ℕ) : ℝ) ≤ (((2 * r + 2) * W.length : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      calc ‖Dw w₁ a g‖ * ‖Dw w₂ F g‖
          ≤ (‖Lid‖ * Cχ * gN g ^ (0 + (2 * r + 2) * w₁.length)) * (max c 0 * gN g ^ (-A₀)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
        _ = ‖Lid‖ * Cχ * max c 0 * gN g ^ ((((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀)) := by
            rw [Real.rpow_add hgp, Real.rpow_natCast, zero_add]; ring
        _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg1 hex) (by positivity))
  refine hb.trans ?_
  have h2 : (2 : ℝ) ^ W.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hW)
  rw [hM]
  calc 2 ^ W.length * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)))
      ≤ 2 ^ N * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

lemma phi_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (mm : ℕ) :
    CkOn mm (GV k r) (Rw w (C6.cutAll D χ₀ de L F)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted mm W → ∀ g ∈ GV k r,
      ‖Dw W (Rw w (C6.cutAll D χ₀ de L F)) g‖ ≤
        C * gN g ^ (-A₀ + (((2 * r + 2) * (W.length + w.length) : ℕ) : ℝ)) := by
  obtain ⟨hck, C, hC0, hC⟩ := fc_bound D hχ de L hF (mm + w.length)
  have hwR : ∀ x ∈ wR w, inLie k r x.2 := fun x hx => by
    simp only [wR, List.mem_map] at hx; obtain ⟨X, hX, rfl⟩ := hx; exact hw X hX
  constructor
  · rw [← Dw_wR]
    apply CkOn_Dw hwR
    have : ((mm : ℕ∞) + ((wR w).length : ℕ∞)) = ((mm + w.length : ℕ) : ℕ∞) := by simp [wR]
    rw [this]; exact hck
  · set cw : ℝ := (w.map nz).prod with hcw
    have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (nz_pos X).le
    refine ⟨cw * C, mul_nonneg hcw0 hC0, fun W hW g hg => ?_⟩
    obtain ⟨u, v, hu, hv, hl, rfl⟩ := hW
    have hvn : ∀ X ∈ w.map nrm, unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact nrm_unit (hw Y hY)
    have e1 : Dw (wL u ++ wR v) (Rw w (C6.cutAll D χ₀ de L F)) g =
        ((cw : ℝ) : ℂ) • Dw (wL u ++ wR (v ++ w.map nrm)) (C6.cutAll D χ₀ de L F) g := by
      rw [Rw_scale, Dw_smul]
      simp only [hcw]
      congr 1
      rw [← Dw_wR, ← Dw_append]
      simp [wR, List.append_assoc]
    have hA : admitted (mm + w.length) (wL u ++ wR (v ++ w.map nrm)) :=
      ⟨u, v ++ w.map nrm, hu, fun X hX => (List.mem_append.1 hX).elim (hv X) (hvn X), by simp; omega, rfl⟩
    rw [e1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hlen' : (wL u ++ wR (v ++ w.map nrm)).length = (wL u ++ wR v).length + w.length := by
      simp [wL, wR]; ring
    rw [← hlen']
    exact hC _ hA g hg

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem budget_class_estimate : C6.BudgetClass := by
  intro k r Wp Wq _ _ _ _ _ D nf fib L o κ Θ ε de χ₀ A₀ F hε hde hχ hfib hΘ hF hsupp mm
  obtain ⟨_, ⟨δ₀, hδ₀, hχ0⟩, _⟩ := id hχ
  set Fc := C6.cutAll D χ₀ de L F with hFc
  set O : Set (Mat k r) := {g | Gf k r D.z D.z' g < ε} ∪
    ⋃ l ∈ L, {g | Complex.normSq (Dmin k r D.z D.z' g l) < δ₀ * de} with hOdef
  have hO : IsOpen O := (isOpen_lt (Gf_cont D.z D.z') continuous_const).union
    (isOpen_biUnion fun l _ => isOpen_lt (Complex.continuous_normSq.comp (Dmin_cont D.z D.z' l)) continuous_const)
  set S : Set (Mat k r) := {g | g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g ∧
    ∀ l ∈ L, δ₀ * de ≤ Complex.normSq (Dmin k r D.z D.z' g l)} with hSdef
  have hSG : S ⊆ GV k r := fun g hg => hg.1
  have hnotO : ∀ g ∈ GV k r, g ∉ O → g ∈ S := by
    intro g hg hgO
    simp only [hOdef, mem_union, mem_setOf_eq, mem_iUnion, not_or, not_lt, not_exists] at hgO
    exact ⟨hg, hgO.1, fun l hl => hgO.2 l hl⟩
  have hdd : 0 < δ₀ * de := mul_pos hδ₀ hde
  have hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ C6.domL D L := by
    intro g hg
    by_cases hgO : g ∈ O
    · exact Or.inl hgO
    · right
      obtain ⟨_, h1, h2⟩ := hnotO g hg hgO
      refine ⟨hg, lt_of_lt_of_le hε h1, fun l hl h0 => ?_⟩
      have := h2 l hl
      rw [h0, map_zero] at this
      linarith
  have hFc0 : ∀ g ∈ GV k r, g ∈ O → Fc g = 0 := by
    intro g hg hgO
    simp only [hOdef, mem_union, mem_setOf_eq, mem_iUnion] at hgO
    rcases hgO with h | ⟨l, hl, h⟩
    · have : F g = 0 := by
        by_contra hne; exact absurd (hsupp g hg hne) (not_le.2 h)
      simp [hFc, C6.cutAll, this]
    · have : C6.chiAll D χ₀ de L g = 0 := by
        apply Finset.prod_eq_zero hl
        apply hχ0
        rw [div_lt_iff₀ hde]; linarith
      simp [hFc, C6.cutAll, this]
  set c₀ : ℝ := min (δ₀ * de) (min ε (ε ^ 2)) with hc₀
  have hc₀p : 0 < c₀ := lt_min hdd (lt_min hε (by positivity))
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · exact (min_le_left _ _).trans (hg.2.2 l hl)
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg.2.1
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2.1
    have : ε ^ 2 ≤ Gf k r D.z D.z' g * Gf k r D.z D.z' g := by nlinarith
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans this
  have hS' : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g := fun g hg => ⟨hg.1, hg.2.1⟩
  set V₀ : Set (Mat k r) := {g | 0 < Gf k r D.z D.z' g} ∩ ⋂ l ∈ L, {g | Dmin k r D.z D.z' g l ≠ 0} with hV₀
  have hV₀o : IsOpen V₀ := (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter
    (isOpen_biInter_finset fun l _ => isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const)
  have hSV : S ⊆ V₀ := by
    intro g hg
    refine ⟨lt_of_lt_of_le hε hg.2.1, mem_iInter₂.2 fun l hl => ?_⟩
    intro h0
    have := hg.2.2 l hl
    rw [show Dmin k r D.z D.z' g l = 0 from h0, map_zero] at this
    linarith
  show InCC _ mm (fun g => (Θ.map fun T => T.coef g (Rw T.word Fc g)).sum)
  apply InCC_opsum Θ (fun T g => T.coef g (Rw T.word Fc g))
  intro T hT
  obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := hΘ.2.2 T hT
  obtain ⟨hΦck, CΦ, hCΦ0, hCΦ⟩ := phi_bound D hχ de L hF T.word T.word_lie mm
  have hcU := ubl_coefP D fib hfib L P a b c es hP hab hlie hε hS' hc₀p hSD hSGf mm
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  have hcT := ub_congr hV₀o hSV hSG (fun g hG hV => hco g ⟨hG, hV.1, fun l hl => mem_iInter₂.1 hV.2 l hl⟩) hUB
  have hPr : Pr O (C6.domL D L) mm T.coef (Rw T.word Fc) :=
    ⟨sCkOn_mono le_top (hΘ.1 T hT).1, hΦck, Rw_vanish hO T.word_lie hFc0⟩
  set fo := (es.map fun e => e.2.length).sum with hfo
  set γ := 3 * (r + 1) with hγ
  refine ⟨2 ^ mm * (Cc * CΦ), hPr.ck hO hcov, fun u v hu hv hl g hg => ?_⟩
  rw [dLR_eq]
  show gN g ^ _ * ‖Dw (wL u ++ wR v) (ap T.coef (Rw T.word Fc)) g‖ ≤ _
  have hW : admitted mm (wL u ++ wR v) := ⟨u, v, hu, hv, hl, rfl⟩
  have hlieW := admissible_word_mem_lie hW
  have hgp := gN_pos hg
  have hg1 := gN_ge_one hg
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlieW (hPr.mono zero_le).apz g hg hgO, norm_zero, mul_zero]
    positivity
  · have hgS := hnotO g hg hgO
    set W := wL u ++ wR v
    set e₀ : ℝ := (κ : ℝ) + (γ : ℝ) * ((o : ℝ) + mm) - A₀ with he₀
    set M := Cc * CΦ * gN g ^ e₀ with hM
    have hb := leib_bound hO hcov g hg M W T.coef (Rw T.word Fc) hlieW
      (hPr.mono (by exact_mod_cast admissible_word_length_le hW)) (by
        intro w₁ w₂ h₁ h₂ hl12
        have b1 := hcT w₁ (Adm_sub h₁ hW) g hgS
        have b2 := hCΦ w₂ (Adm_sub h₂ hW) g hg
        have hWl := admissible_word_length_le hW
        have hN : γ * fo + γ * w₁.length + (2 * r + 2) * (w₂.length + T.word.length) ≤ γ * (o + mm) := by
          have h1 : (2 * r + 2) * (w₂.length + T.word.length) ≤ γ * (w₂.length + T.word.length) :=
            Nat.mul_le_mul_right _ (by omega)
          have h2 : γ * fo + γ * w₁.length + γ * (w₂.length + T.word.length) ≤ γ * (o + mm) := by
            rw [← mul_add, ← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
          omega
        have hNr : ((γ * fo + γ * w₁.length + (2 * r + 2) * (w₂.length + T.word.length) : ℕ) : ℝ) ≤
            ((γ * (o + mm) : ℕ) : ℝ) := by exact_mod_cast hN
        have hex : ((κ + γ * fo + γ * w₁.length : ℕ) : ℝ) + (-A₀ + (((2 * r + 2) * (w₂.length +
            T.word.length) : ℕ) : ℝ)) ≤ e₀ := by
          rw [he₀]; push_cast at hNr ⊢; linarith
        calc ‖Dw w₁ T.coef g‖ * ‖Dw w₂ (Rw T.word Fc) g‖
            ≤ (Cc * gN g ^ (κ + γ * fo + γ * w₁.length)) *
              (CΦ * gN g ^ (-A₀ + (((2 * r + 2) * (w₂.length + T.word.length) : ℕ) : ℝ))) :=
              mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hCc0 (by positivity))
          _ = Cc * CΦ * (gN g ^ (((κ + γ * fo + γ * w₁.length : ℕ) : ℝ)) *
              gN g ^ (-A₀ + (((2 * r + 2) * (w₂.length + T.word.length) : ℕ) : ℝ))) := by
              rw [Real.rpow_natCast]; ring
          _ = Cc * CΦ * gN g ^ (((κ + γ * fo + γ * w₁.length : ℕ) : ℝ) +
              (-A₀ + (((2 * r + 2) * (w₂.length + T.word.length) : ℕ) : ℝ))) := by
              rw [← Real.rpow_add hgp]
          _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg1 hex)
              (mul_nonneg hCc0 hCΦ0))
    have hA : gN g ^ (A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o)) * gN g ^ e₀ = 1 := by
      rw [← Real.rpow_add hgp, he₀, hγ]
      have : A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o) + ((κ : ℝ) + ((3 * (r + 1) : ℕ) : ℝ) * ((o : ℝ) + mm) - A₀)
          = 0 := by push_cast; ring
      rw [this, Real.rpow_zero]
    have h2 : (2 : ℝ) ^ W.length ≤ 2 ^ mm := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hW)
    calc gN g ^ (A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o)) * ‖Dw W (ap T.coef (Rw T.word Fc)) g‖
        ≤ gN g ^ (A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o)) * (2 ^ W.length * M) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 ^ W.length * (Cc * CΦ) * (gN g ^ (A₀ - κ - 3 * ((r : ℝ) + 1) * ((mm : ℝ) + o)) * gN g ^ e₀) := by
          rw [hM]; ring
      _ = 2 ^ W.length * (Cc * CΦ) := by rw [hA, mul_one]
      _ ≤ 2 ^ mm * (Cc * CΦ) := mul_le_mul_of_nonneg_right h2 (mul_nonneg hCc0 hCΦ0)

end Formalism.FourierDecayAlt.P
