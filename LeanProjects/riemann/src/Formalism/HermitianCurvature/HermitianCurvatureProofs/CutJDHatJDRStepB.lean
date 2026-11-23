import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepBRules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open scoped ContDiff

section point

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem posL_cI_comp {t : ℕ} (a : Fin t → Fin (2 * r + k + 1)) : posL k r 0 ∘ (cI ∘ a) = a :=
  funext fun l => posL_cI _

theorem la_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    {x : Mx k r} (hx : x ∈ Glev k r 0 ∩ D) :
    La hD ⟨cut k r 0 D f, cut_mem hD hf⟩ x (qminor (EA hD) a b u) = qminorOp (EH k r) a b u f x := by
  rw [La_apply]
  have e1 : ((qminor (EA (E := E) hD) a b u : SA E hD) : Module.End ℂ (VS k r 0 D E)) =
      qminor (Eh (E := E) (i := 0) hD) (cI ∘ a) (cI ∘ b) u := by
    have := map_qminor (SA E hD).val (EA hD) a b u
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ _ _ hx]
  have hloc := (good_qminor (E := E) hD (cI ∘ a) (cI ∘ b) u).loc (cut k r 0 D f) f
    (fun x' hx' => cut_of_mem _ hx') _ hx
  rw [posL_cI_comp, posL_cI_comp] at hloc
  rw [posL_cI_comp, posL_cI_comp]
  exact hloc

include hD in
theorem sm_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    SmoothLev k r 0 D (qminorOp (EH k r) a b u f) := by
  have h := (good_qminor (E := E) hD (cI ∘ a) (cI ∘ b) u).sm f hf
  rw [posL_cI_comp, posL_cI_comp] at h
  exact h

theorem cell_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    wCell k r (Fin.last r) c * g ∈ Glev k r 0 :=
  Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)

theorem cell_cd {g : Mx k r} : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
  Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const

include hD in
theorem nhds_cell {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) :
    ∀ᶠ c' in nhds c, c' ∈ OmX r ∧ wCell k r (Fin.last r) c' * g ∈ Glev k r 0 ∩ D := by
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (cell_cd (g := g)).continuousOn.continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hD.mem_nhds hcD)] with c' h1 h2
  exact ⟨h1, cell_mem h1 hg, h2⟩

theorem pOp_ev {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h : F₁ =ᶠ[nhds c] F₂) :
    pOp l F₁ c = pOp l F₂ c := by
  simp only [pOp, wirt, h.fderiv_eq]

include hD in
theorem diff_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) :
    DifferentiableAt ℝ (fun c' => qminorOp (EH k r) a b u f (wCell k r (Fin.last r) c' * g)) c :=
  Formalism.FourierDecayAlt.P.WeylCellAction.diff_comp (sm_qminor hD hf a b u) (φ := fun c' => wCell k r (Fin.last r) c' * g) cell_cd
    (fun c' hc' => cell_mem hc' hg) hc hcD

theorem la_E (v₀ : VS k r 0 D E) {x : Mx k r} (hx : x ∈ Glev k r 0 ∩ D) (p q : Fin (2 * r + k + 1)) (X : SA E hD) :
    La hD v₀ x (EA hD p q * X) = EH k r p q (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E) x := by
  rw [La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val, ev_E hD _ _ _ hx, posL_cI, posL_cI]

theorem EA_v0B (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) :
    ((EA hD (eI k r a) (wI k r w) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ = 0 := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (wI k r w))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (wI k r w) (cut k r 0 D f) g = 0
    rw [hloc, rightRuleB z' D f hz' hD hf hRf g hg a ha w]
  · show ((Eh hD (cI (eI k r a)) (cI (wI k r w)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g = 0
    rw [(Eh hD (cI (eI k r a)) (cI (wI k r w)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg]

end point

section pt

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rowsN_val (l : Fin (r + 1)) (s : Fin (k + 1)) (j : Fin (r - l.val + k)) :
    (rowsN k r l s j).val = if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1 := by
  unfold rowsN
  split_ifs <;> rfl

theorem stepB_pt (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)}
    (hD : IsOpen D) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) (l : ℕ) (hl : l + 2 ≤ r) (s t : Fin (k + 1)) (u : ℂ) :
    qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t) u f (wCell k r (Fin.last r) c * g) =
      u • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (u - 1) f
          (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (fun c' => qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
          (rowsN k r ⟨l + 1, by omega⟩ t) (u - 1) f (wCell k r (Fin.last r) c' * g)) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (u - 1 - 1) f (wCell k r (Fin.last r) c * g) := by
  set x0 := wCell k r (Fin.last r) c * g with hx0def
  have hx0 : x0 ∈ Glev k r 0 ∩ D := ⟨cell_mem hc hg, hcD⟩
  set v₀ : VS k r 0 D E := ⟨cut k r 0 D f, cut_mem hD hf⟩ with hv₀
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := leftEq_cut z hN hLf
  set Λ := La hD v₀ x0 with hΛ
  set tt := r - l - 2 + k with htt
  have hT : tt + 2 = r - (⟨l, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT1 : tt + 1 = r - (⟨l + 1, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT2 : tt = r - (⟨l + 2, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  set a := rowsN k r ⟨l, by omega⟩ s ∘ Fin.cast hT with ha
  set b := rowsN k r ⟨l, by omega⟩ t ∘ Fin.cast hT with hb
  have hav : ∀ m : Fin (tt + 2), (a m).val = if m.val < r - l + s.val then l + m.val else l + m.val + 1 := by
    intro m; simp only [ha, Function.comp_apply, rowsN_val, Fin.val_cast, Fin.val_mk]
  have hbv : ∀ m : Fin (tt + 2), (b m).val = if m.val < r - l + t.val then l + m.val else l + m.val + 1 := by
    intro m; simp only [hb, Function.comp_apply, rowsN_val, Fin.val_cast, Fin.val_mk]
  have hab_le : ∀ m : Fin (tt + 2), (a m).val ≤ r + k ∧ (b m).val ≤ r + k := by
    intro m
    have := m.isLt
    rw [hav, hbv]
    constructor <;> split_ifs <;> omega

  have hLmid : ∀ p : Fin (2 * r + k + 1), l + 2 ≤ p.val → p.val ≤ r + k → ∀ X : SA E hD,
      Λ (EA hD p (eI k r ⟨l, by omega⟩) * X) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    by_cases hpr : p.val < r
    · have hpe : p = eI k r ⟨p.val, hpr⟩ := Fin.ext (by simp [eI])
      rw [hpe, Formalism.FourierDecayAlt.P.left_rule_cell E k r z D _ hz hD hN hsm hle c hc g hg hcD ⟨p.val, hpr⟩ ⟨l, by omega⟩
        (by simp; omega), if_neg (by simp; omega), zero_smul]
    · have hpw : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
      rw [hpw, leftRuleB z D _ hz hD hN hsm hle c hc g hg hcD ⟨l, by omega⟩ (by simp; omega)]
  have hL1 : ∀ X : SA E hD, Λ (EA hD (eI k r ⟨l + 1, by omega⟩) (eI k r ⟨l, by omega⟩) * X) =
      (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • Λ X := by
    intro X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    rw [Formalism.FourierDecayAlt.P.left_rule_cell E k r z D _ hz hD hN hsm hle c hc g hg hcD ⟨l + 1, by omega⟩ ⟨l, by omega⟩
      (by simp), if_pos (by simp), La_apply]
  have hRmid : ∀ p : Fin (2 * r + k + 1), l + 2 ≤ p.val → p.val ≤ r + k → ∀ X : SA E hD,
      Λ (X * EA hD (eI k r ⟨l, by omega⟩) p) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    have hzero : ((EA hD (eI k r ⟨l, by omega⟩) p : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ = 0 := by
      by_cases hpr : p.val < r
      · have hpe : p = eI k r ⟨p.val, hpr⟩ := Fin.ext (by simp [eI])
        rw [hpe, hv₀, root_vector_action_cutoff hD z' hz' Formalism.FourierDecayAlt.P.right_rule_derivative hf hRf ⟨l, by omega⟩ ⟨p.val, hpr⟩ (by simp; omega),
          if_neg (by simp; omega), zero_smul]
      · have hpw : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
        rw [hpw, hv₀, EA_v0B hD z' hz' hf hRf ⟨l, by omega⟩ (by simp; omega)]
    rw [hzero, map_zero]
    rfl
  have hR1 : ∀ X : SA E hD, Λ (X * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨l + 1, by omega⟩)) = Λ X := by
    intro X
    rw [hΛ, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    rw [hv₀, root_vector_action_cutoff hD z' hz' Formalism.FourierDecayAlt.P.right_rule_derivative hf hRf ⟨l, by omega⟩ ⟨l + 1, by omega⟩ (by simp),
      if_pos (by simp), one_smul]
  have hne : eI k r ⟨l, by omega⟩ ≠ eI k r ⟨l + 1, by omega⟩ := by simp [eI, Fin.ext_iff]
  have hring := stepB_ring (EA (E := E) hD) (EA_gl hD) Λ (eI k r ⟨l, by omega⟩) (eI k r ⟨l + 1, by omega⟩) hne
    (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) a b
    (Fin.ext (by rw [hav]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hav]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hbv]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hbv]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (fun m hm h => by have := congrArg Fin.val h; rw [hav] at this; simp [eI] at this; split_ifs at this <;> omega)
    (fun m hm h => by have := congrArg Fin.val h; rw [hbv] at this; simp [eI] at this; split_ifs at this <;> omega)
    (fun m hm X => hLmid (a m) (by rw [hav]; split_ifs <;> omega) (hab_le m).1 X) hL1
    (fun m hm X => hRmid (b m) (by rw [hbv]; split_ifs <;> omega) (hab_le m).2 X) hR1 u

  have hc1 : a ∘ Fin.succ = rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsN_val]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hd1 : b ∘ Fin.succ = rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsN_val]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hc2 : (fun j : Fin tt => a ⟨j.val + 2, by omega⟩) = rowsN k r ⟨l + 2, by omega⟩ s ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsN_val]
    simp only [Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hd2 : (fun j : Fin tt => b ⟨j.val + 2, by omega⟩) = rowsN k r ⟨l + 2, by omega⟩ t ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsN_val]
    simp only [Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  rw [hc1, hd1, hc2, hd2] at hring

  have hread : ∀ {t' : ℕ} (a' b' : Fin t' → Fin (2 * r + k + 1)) (w : ℂ) (x : Mx k r), x ∈ Glev k r 0 ∩ D →
      La hD v₀ x (qminor (EA hD) a' b' w) = qminorOp (EH k r) a' b' w f x :=
    fun a' b' w x hx => la_qminor hD hf a' b' w hx
  rw [hΛ, hread _ _ _ _ hx0, hread _ _ _ _ hx0, ← hΛ] at hring
  rw [ha, hb] at hring
  simp only [top_qminor_cast] at hring
  rw [hring]

  congr 1
  set Q1 := qminor (EA (E := E) hD) (rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1)
    (rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1) (u - 1) with hQ1
  have hT' : Λ (Tm (EA hD) u (eI k r ⟨l, by omega⟩) (eI k r ⟨l, by omega⟩) * Q1) =
      u • Λ Q1 + EH k r (eI k r ⟨l, by omega⟩) (eI k r ⟨l, by omega⟩)
        (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E) x0 := by
    unfold Tm
    rw [if_pos rfl, add_mul, map_add, la_E hD v₀ hx0, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul]
  rw [hT', Formalism.FourierDecayAlt.P.torus_cell E k r D _ hD (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    c hc g hg hcD ⟨l, by omega⟩]
  rw [hΛ, hread _ _ _ _ hx0, top_qminor_cast]
  congr 1
  apply pOp_ev
  filter_upwards [nhds_cell hD hc hg hcD] with c' hc'
  have := hread (rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1) (rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1) (u - 1) _ hc'.2
  rw [La_apply, top_qminor_cast] at this
  exact this

end pt

section asm

variable {k r : ℕ}

theorem uC_step (l : ℕ) (hl : l + 1 ≤ r) (Y : ℂ) :
    Q.uC k r ⟨l + 1, by omega⟩ Y = Q.uC k r ⟨l, by omega⟩ Y - 1 := by
  simp only [Q.uC, Q.mdim, Fin.val_mk]
  have e : r - l = r - (l + 1) + 1 := by omega
  rw [e]
  push_cast
  ring

theorem uC_gauge (l : ℕ) (hl : l < r) (Y : ℂ) :
    Q.uC k r ⟨l, by omega⟩ Y = Y + ((Mdim k r ⟨l, hl⟩ - 1 : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Mdim, Fin.val_mk]
  have e : 2 * (r - l) + k + 1 - 1 = 2 * (r - l) + k := by omega
  rw [e]
  push_cast
  ring

theorem has_fderiv_double_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (κ : ι → ι' → ℂ) (F : ι → ι' → (Fin r → ℂ) → E) {c : Fin r → ℂ} (hF : ∀ i j, DifferentiableAt ℝ (F i j) c) :
    HasFDerivAt (fun c' => ∑ i, ∑ j, κ i j • F i j c') (∑ i, ∑ j, κ i j • fderiv ℝ (F i j) c) c := by
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hF i j).hasFDerivAt.const_smul (κ i j)

theorem partial_derivative_double_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (κ : ι → ι' → ℂ) (F : ι → ι' → (Fin r → ℂ) → E) {c : Fin r → ℂ} (hF : ∀ i j, DifferentiableAt ℝ (F i j) c)
    (l : Fin r) (hc : c ∈ OmX r) :
    pOp l (fun c' => ∑ i, ∑ j, κ i j • F i j c') c = ∑ i, ∑ j, κ i j • pOp l (F i j) c := by
  simp only [pOp, if_pos hc, wirt, (has_fderiv_double_sum κ F hF).fderiv, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

theorem fin_alg {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (w Y n c1 c0 : ℂ) (κ : ι → ι' → ℂ) (A P B : ι → ι' → E) :
    w • ∑ i, ∑ j, κ i j • ((Y + n) • A i j + P i j - (c1 / c0) • B i j) =
      Y • (w • ∑ i, ∑ j, κ i j • A i j) + w • (∑ i, ∑ j, κ i j • P i j + n • ∑ i, ∑ j, κ i j • A i j) -
        c1 • (c0⁻¹ • (w • ∑ i, ∑ j, κ i j • B i j)) := by
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [div_eq_mul_inv]
  module

end asm

end Formalism.FourierDecayAlt.P.CutMP.StepB

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBN.MC Formalism.FourierDecayAlt.P.CutMP.StepB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem residue_second_move_holds : JDRStepB := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ l hl c hc g hg hcg
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  have hDo : IsOpen D := hD.1
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 := ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ x ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * x ∈ D := by
    intro x hx n hn
    have := hD.2 x hx n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (k + 1) → Fin (k + 1) → ℂ, κ = fun (s t : Fin (k + 1)) =>
    ((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t) := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : (Fin r → ℂ) → ℂ,
    wt = fun c' => ((∏ a : Fin r, ‖c' a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hFN : ∀ (m : ℕ) (hm : m ≤ r), ∀ c' ∈ OmX r, FN k r z z' Y J ⟨m, by omega⟩ c' g =
      wt c' • ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨m, by omega⟩ s) (rowsN k r ⟨m, by omega⟩ t)
        (Q.uC k r ⟨m, by omega⟩ Y) J (wCell k r (Fin.last r) c' * g) := by
    intro m hm c' hc'
    subst hκ hwt
    unfold FN NL
    rw [resG_last, inv_wCell_last_mul_mulVec_of_inWb hc' hg hz]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, cOp, ciOp]

  obtain ⟨F1, hF1⟩ : ∃ F1 : Fin (k + 1) → Fin (k + 1) → (Fin r → ℂ) → (Wq →L[ℂ] Wp), F1 = fun s t c' =>
    qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J
      (wCell k r (Fin.last r) c' * g) := ⟨_, rfl⟩
  have hd1 : ∀ s t, DifferentiableAt ℝ (F1 s t) c := fun s t => by
    rw [hF1]
    exact diff_qminor hDo hf _ _ _ hc hg hcg
  have hp1 : pOp ⟨l, by omega⟩ (fun c' => FN k r z z' Y J ⟨l + 1, by omega⟩ c' g) c =
      wt c • (∑ s, ∑ t, κ s t • pOp ⟨l, by omega⟩ (F1 s t) c +
        (((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • ∑ s, ∑ t, κ s t • F1 s t c) := by
    rw [Formalism.FourierDecayAlt.P.PBN.pOp_locO ⟨l, by omega⟩ (fun c' hc' => hFN (l + 1) (by omega) c' hc') hc]
    have eF : ∀ c', (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t)
        (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c' * g)) = ∑ s, ∑ t, κ s t • F1 s t c' := by
      intro c'; rw [hF1]
    simp only [eF]
    subst hwt
    beta_reduce
    have hdH : DifferentiableAt ℝ (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c :=
      (has_fderiv_double_sum κ F1 hd1).differentiableAt
    have hG := Formalism.FourierDecayAlt.P.gauge_positivity (Wq →L[ℂ] Wp) r (fun a => Mdim k r a - 1)
      (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c hc hdH ⟨l, by omega⟩
    rw [hG, partial_derivative_double_sum κ F1 hd1 ⟨l, by omega⟩ hc]
  rw [hp1, hFN l (by omega) c hc, hFN (l + 1) (by omega) c hc, hFN (l + 2) (by omega) c hc]

  have hpt : ∀ s t, qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t) (Q.uC k r ⟨l, by omega⟩ Y)
      J (wCell k r (Fin.last r) c * g) =
      (Y + ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
          (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (F1 s t) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (Q.uC k r ⟨l + 2, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) := by
    intro s t
    have h := stepB_pt z z' hz hz' hDo hN hf hLf hRf hc hg hcg l hl s t (Q.uC k r ⟨l, by omega⟩ Y)
    rw [uC_step (k := k) (l + 1) (by omega) Y, uC_step (k := k) l (by omega) Y]
    rw [hF1]
    rw [uC_step (k := k) l (by omega) Y, ← uC_gauge (k := k) l (by omega) Y]
    exact h
  have hL : (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t)
      (Q.uC k r ⟨l, by omega⟩ Y) J (wCell k r (Fin.last r) c * g)) =
      ∑ s, ∑ t, κ s t • ((Y + ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r)
          (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J
            (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (F1 s t) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (Q.uC k r ⟨l + 2, by omega⟩ Y) J (wCell k r (Fin.last r) c * g)) :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [hpt s t]
  have hA : (∑ s, ∑ t, κ s t • F1 s t c) = ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
      (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) := by
    rw [hF1]
  rw [hL, hA]
  exact fin_alg _ _ _ _ _ _ _ _ _

end Formalism.FourierDecayAlt.P.CutMP
