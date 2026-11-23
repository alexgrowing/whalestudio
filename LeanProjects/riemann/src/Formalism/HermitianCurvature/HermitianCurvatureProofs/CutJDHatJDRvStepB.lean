import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepBRules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pt

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rowsNv_val (l : Fin (r + 1)) (s : Fin (k + 1)) (j : Fin (r - l.val + k)) :
    (rowsNv k r l s j).val = if j.val < s.val then r + j.val else r + j.val + 1 := by
  unfold rowsNv
  split_ifs <;> rfl

theorem pbOp_ev {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h : F₁ =ᶠ[nhds c] F₂) :
    pbOp l F₁ c = pbOp l F₂ c := by
  simp only [pbOp, wirtBar, h.fderiv_eq]

theorem EA_v0Bv {D : Set (Mx k r)} (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) :
    ((EA hD (wI k r w) (esI k r a) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ = 0 := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (wI k r w)) (cI (esI k r a))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (wI k r w) (esI k r a) (cut k r 0 D f) g = 0
    rw [hloc, rightRuleBv z' D f hz' hD hf hRf g hg a ha w]
  · show ((Eh hD (cI (wI k r w)) (cI (esI k r a)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g = 0
    rw [(Eh hD (cI (wI k r w)) (cI (esI k r a)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg]

theorem stepBv_pt (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)}
    (hD : IsOpen D) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) (l : ℕ) (hl : l + 2 ≤ r) (s t : Fin (k + 1)) (w : ℂ) :
    qminorOp (EH k r) (rowsNv k r ⟨l, by omega⟩ s) (rowsNv k r ⟨l, by omega⟩ t) w f (wCell k r (Fin.last r) c * g) =
      (w - ((r - l - 1 + k : ℕ) : ℂ)) • qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s)
          (rowsNv k r ⟨l + 1, by omega⟩ t) w f (wCell k r (Fin.last r) c * g) -
        pbOp ⟨l, by omega⟩ (fun c' => qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s)
          (rowsNv k r ⟨l + 1, by omega⟩ t) w f (wCell k r (Fin.last r) c' * g)) c -
        (star (c ⟨l + 1, by omega⟩) / star (c ⟨l, by omega⟩)) • qminorOp (EH k r) (rowsNv k r ⟨l + 2, by omega⟩ s)
          (rowsNv k r ⟨l + 2, by omega⟩ t) w f (wCell k r (Fin.last r) c * g) := by
  set x0 := wCell k r (Fin.last r) c * g with hx0def
  have hx0 : x0 ∈ Glev k r 0 ∩ D := ⟨cell_mem hc hg, hcD⟩
  set v₀ : VS k r 0 D E := ⟨cut k r 0 D f, cut_mem hD hf⟩ with hv₀
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := leftEq_cut z hN hLf
  set Λ := La hD v₀ x0 with hΛ
  set tt := r - l - 2 + k with htt
  have hT : tt + 2 = r - (⟨l, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT1 : tt + 1 = r - (⟨l + 1, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT2 : tt = r - (⟨l + 2, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  set a := rowsNv k r ⟨l, by omega⟩ s ∘ Fin.cast hT with ha
  set b := rowsNv k r ⟨l, by omega⟩ t ∘ Fin.cast hT with hb
  have hav : ∀ m : Fin (tt + 2), (a m).val = if m.val < s.val then r + m.val else r + m.val + 1 := by
    intro m; simp only [ha, Function.comp_apply, rowsNv_val, Fin.val_cast]
  have hbv : ∀ m : Fin (tt + 2), (b m).val = if m.val < t.val then r + m.val else r + m.val + 1 := by
    intro m; simp only [hb, Function.comp_apply, rowsNv_val, Fin.val_cast]
  have hsk : s.val ≤ k := Nat.lt_succ_iff.mp s.isLt
  have htk : t.val ≤ k := Nat.lt_succ_iff.mp t.isLt

  have hLmid : ∀ p : Fin (2 * r + k + 1), r ≤ p.val → p.val + l + 2 ≤ 2 * r + k → ∀ X : SA E hD,
      Λ (EA hD (esI k r ⟨l, by omega⟩) p * X) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    by_cases hpw : p.val ≤ r + k
    · have hpe : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
      rw [hpe, leftRuleBv z D _ hz hD hN hsm hle c hc g hg hcD ⟨l, by omega⟩ (by simp; omega)]
    · have hpe : p = esI k r ⟨2 * r + k - p.val, by omega⟩ := Fin.ext (by simp [esI]; omega)
      rw [hpe, Formalism.FourierDecayAlt.P.CutMP.TVG.mirror_left_rule_cell_holds E k r z D _ hz hD hN hsm hle c hc g hg hcD
        ⟨2 * r + k - p.val, by omega⟩ ⟨l, by omega⟩ (by simp; omega), if_neg (by simp; omega), zero_smul]
  have hL1 : ∀ X : SA E hD, Λ (EA hD (esI k r ⟨l, by omega⟩) (esI k r ⟨l + 1, by omega⟩) * X) =
      (star (c ⟨l + 1, by omega⟩) / star (c ⟨l, by omega⟩)) • Λ X := by
    intro X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    rw [Formalism.FourierDecayAlt.P.CutMP.TVG.mirror_left_rule_cell_holds E k r z D _ hz hD hN hsm hle c hc g hg hcD ⟨l + 1, by omega⟩
      ⟨l, by omega⟩ (by simp), if_pos (by simp), La_apply]
  have hRmid : ∀ p : Fin (2 * r + k + 1), r ≤ p.val → p.val + l + 2 ≤ 2 * r + k → ∀ X : SA E hD,
      Λ (X * EA hD p (esI k r ⟨l, by omega⟩)) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    have hzero : ((EA hD p (esI k r ⟨l, by omega⟩) : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ = 0 := by
      by_cases hpw : p.val ≤ r + k
      · have hpe : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
        rw [hpe, hv₀, EA_v0Bv hD z' hz' hf hRf ⟨l, by omega⟩ (by simp; omega)]
      · have hpe : p = esI k r ⟨2 * r + k - p.val, by omega⟩ := Fin.ext (by simp [esI]; omega)
        rw [hpe, hv₀, Formalism.FourierDecayAlt.P.CutMP.TVG.root_action_on_truncated_vector hD z' hz' Formalism.FourierDecayAlt.P.CutMP.TVG.mirror_right_rule_holds hf hRf
          ⟨2 * r + k - p.val, by omega⟩ ⟨l, by omega⟩ (by simp; omega), if_neg (by simp; omega), zero_smul]
    rw [hzero, map_zero]
    rfl
  have hR1 : ∀ X : SA E hD, Λ (X * EA hD (esI k r ⟨l + 1, by omega⟩) (esI k r ⟨l, by omega⟩)) = Λ X := by
    intro X
    rw [hΛ, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    rw [hv₀, Formalism.FourierDecayAlt.P.CutMP.TVG.root_action_on_truncated_vector hD z' hz' Formalism.FourierDecayAlt.P.CutMP.TVG.mirror_right_rule_holds hf hRf
      ⟨l + 1, by omega⟩ ⟨l, by omega⟩ (by simp), if_pos (by simp), one_smul]
  have hne : esI k r ⟨l, by omega⟩ ≠ esI k r ⟨l + 1, by omega⟩ := by simp [esI, Fin.ext_iff]; omega
  have hvalL : ∀ m : Fin tt, r ≤ (a m.castSucc.castSucc).val ∧ (a m.castSucc.castSucc).val + l + 2 ≤ 2 * r + k := by
    intro m
    have := m.isLt
    rw [hav]
    simp only [Fin.coe_castSucc]
    constructor <;> split_ifs <;> omega
  have hvalLb : ∀ m : Fin tt, r ≤ (b m.castSucc.castSucc).val ∧ (b m.castSucc.castSucc).val + l + 2 ≤ 2 * r + k := by
    intro m
    have := m.isLt
    rw [hbv]
    simp only [Fin.coe_castSucc]
    constructor <;> split_ifs <;> omega
  have hring := stepBv_ring (EA (E := E) hD) (EA_gl hD) Λ (esI k r ⟨l, by omega⟩) (esI k r ⟨l + 1, by omega⟩) hne
    (star (c ⟨l + 1, by omega⟩) / star (c ⟨l, by omega⟩)) a b
    (Fin.ext (by rw [hav]; simp [esI]; split_ifs <;> omega))
    (Fin.ext (by rw [hav]; simp [esI]; split_ifs <;> omega))
    (Fin.ext (by rw [hbv]; simp [esI]; split_ifs <;> omega))
    (Fin.ext (by rw [hbv]; simp [esI]; split_ifs <;> omega))
    (fun m h => by have h1 := congrArg Fin.val h; have h2 := hvalL m; simp only [esI, Fin.val_mk] at h1; omega)
    (fun m h => by have h1 := congrArg Fin.val h; have h2 := hvalLb m; simp only [esI, Fin.val_mk] at h1; omega)
    (fun m X => hRmid _ (hvalL m).1 (hvalL m).2 X) hR1
    (fun m X => hLmid _ (hvalLb m).1 (hvalLb m).2 X) hL1 w

  have hc1 : a ∘ Fin.castSucc = rowsNv k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsNv_val]
    simp only [Fin.coe_castSucc, Fin.val_cast]
  have hd1 : b ∘ Fin.castSucc = rowsNv k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsNv_val]
    simp only [Fin.coe_castSucc, Fin.val_cast]
  have hc2 : a ∘ Fin.castSucc ∘ Fin.castSucc = rowsNv k r ⟨l + 2, by omega⟩ s ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsNv_val]
    simp only [Fin.coe_castSucc, Fin.val_cast]
  have hd2 : b ∘ Fin.castSucc ∘ Fin.castSucc = rowsNv k r ⟨l + 2, by omega⟩ t ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsNv_val]
    simp only [Fin.coe_castSucc, Fin.val_cast]

  set Q1 := qminor (EA (E := E) hD) (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) w with hQ1
  have hcomm : Commute (EA (E := E) hD (esI k r ⟨l, by omega⟩) (esI k r ⟨l, by omega⟩)) Q1 := by
    refine comm_qminor _ (EA_gl hD) _ (fun i h => ?_) (fun i h => ?_) w
    · have h1 := congrArg Fin.val h
      simp only [Function.comp_apply] at h1
      rw [hav] at h1
      have hi := i.isLt
      simp only [Fin.coe_castSucc, esI, Fin.val_mk] at h1
      split_ifs at h1 <;> omega
    · have h1 := congrArg Fin.val h
      simp only [Function.comp_apply] at h1
      rw [hbv] at h1
      have hi := i.isLt
      simp only [Fin.coe_castSucc, esI, Fin.val_mk] at h1
      split_ifs at h1 <;> omega
  have hT' : Λ (Q1 * Tm (EA hD) (w - ((tt + 1 : ℕ) : ℂ)) (esI k r ⟨l, by omega⟩) (esI k r ⟨l, by omega⟩)) =
      (w - ((tt + 1 : ℕ) : ℂ)) • Λ Q1 + EH k r (esI k r ⟨l, by omega⟩) (esI k r ⟨l, by omega⟩)
        (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E) x0 := by
    unfold Tm
    rw [if_pos rfl, mul_add, map_add, ← hcomm.eq, la_E hD v₀ hx0, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, map_smul]
  rw [hT', Formalism.FourierDecayAlt.P.CutMP.TVG.mirror_torus_cell_holds E k r D _ hD
    (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1 c hc g hg hcD ⟨l, by omega⟩] at hring

  have hread : ∀ {t' : ℕ} (a' b' : Fin t' → Fin (2 * r + k + 1)) (w' : ℂ) (x : Mx k r), x ∈ Glev k r 0 ∩ D →
      La hD v₀ x (qminor (EA hD) a' b' w') = qminorOp (EH k r) a' b' w' f x :=
    fun a' b' w' x hx => la_qminor hD hf a' b' w' hx
  have hpb : pbOp ⟨l, by omega⟩ (fun c' => (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E)
      (wCell k r (Fin.last r) c' * g)) c = pbOp ⟨l, by omega⟩ (fun c' => qminorOp (EH k r)
        (rowsNv k r ⟨l + 1, by omega⟩ s) (rowsNv k r ⟨l + 1, by omega⟩ t) w f (wCell k r (Fin.last r) c' * g)) c := by
    apply pbOp_ev
    filter_upwards [nhds_cell hD hc hg hcD] with c' hc'
    have := hread (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) w _ hc'.2
    rw [La_apply] at this
    rw [hQ1, this, hc1, hd1, top_qminor_cast]
  rw [hpb, hΛ, hread _ _ _ _ hx0, hread _ _ _ _ hx0, hread _ _ _ _ hx0, hc1, hd1, hc2, hd2, ha, hb] at hring
  simp only [top_qminor_cast] at hring
  rw [hring]
  have e : ((tt + 1 : ℕ) : ℂ) = ((r - l - 1 + k : ℕ) : ℂ) := by congr 1 <;> omega
  rw [e, ← sub_eq_add_neg]

end pt

section asm

variable {k r : ℕ}

theorem uCv_gauge (l : ℕ) (hl : l < r) (Y : ℂ) :
    Q.uC k r (Fin.last r) Y - 1 - ((r - l - 1 + k : ℕ) : ℂ) = Y - ((Mdim k r ⟨l, hl⟩ - 1 : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Mdim, Fin.val_last, Fin.val_mk, Nat.sub_self]
  have e1 : 2 * (r - l) + k + 1 - 1 = 2 * (r - l) + k := by omega
  have e2 : r - l = (r - l - 1) + 1 := by omega
  rw [e1, e2]
  push_cast
  ring

theorem conj_partial_derivative_double_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (κ : ι → ι' → ℂ) (F : ι → ι' → (Fin r → ℂ) → E) {c : Fin r → ℂ} (hF : ∀ i j, DifferentiableAt ℝ (F i j) c)
    (l : Fin r) (hc : c ∈ OmX r) :
    pbOp l (fun c' => ∑ i, ∑ j, κ i j • F i j c') c = ∑ i, ∑ j, κ i j • pbOp l (F i j) c := by
  simp only [pbOp, if_pos hc, wirtBar, (has_fderiv_double_sum κ F hF).fderiv, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

theorem fin_algv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (w Y n c1 c0 : ℂ) (κ : ι → ι' → ℂ) (A P B : ι → ι' → E) :
    w • ∑ i, ∑ j, κ i j • ((Y - n) • A i j - P i j - (c1 / c0) • B i j) =
      Y • (w • ∑ i, ∑ j, κ i j • A i j) - w • (∑ i, ∑ j, κ i j • P i j + n • ∑ i, ∑ j, κ i j • A i j) -
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

theorem mirror_residue_second_move : JDRvStepB := by
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
    ((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t) := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : (Fin r → ℂ) → ℂ,
    wt = fun c' => ((∏ a : Fin r, ‖c' a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hfix : ∀ c' : Fin r → ℂ, ∀ s : Fin (k + 1),
      (wCell k r (Fin.last r) c' * g) *ᵥ bvec (wI k r s) = g *ᵥ bvec (wI k r s) := by
    intro c' s
    rw [← Matrix.mulVec_mulVec]
    exact top_wlist_wb c' _ _ (Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_uwb (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
      (bvec_wI_inWb s))
  have hFN : ∀ (m : ℕ) (hm : m ≤ r), ∀ c' ∈ OmX r, FNv k r z z' Y J ⟨m, by omega⟩ c' g =
      wt c' • ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsNv k r ⟨m, by omega⟩ s) (rowsNv k r ⟨m, by omega⟩ t)
        (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c' * g) := by
    intro m hm c' hc'
    subst hκ hwt
    unfold FNv NLv
    rw [resG_last]
    simp only [hfix c']
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, cbOp, cbiOp]
  obtain ⟨F1, hF1⟩ : ∃ F1 : Fin (k + 1) → Fin (k + 1) → (Fin r → ℂ) → (Wq →L[ℂ] Wp), F1 = fun s t c' =>
    qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s) (rowsNv k r ⟨l + 1, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J
      (wCell k r (Fin.last r) c' * g) := ⟨_, rfl⟩
  have hd1 : ∀ s t, DifferentiableAt ℝ (F1 s t) c := fun s t => by
    rw [hF1]
    exact diff_qminor hDo hf _ _ _ hc hg hcg
  have hp1 : pbOp ⟨l, by omega⟩ (fun c' => FNv k r z z' Y J ⟨l + 1, by omega⟩ c' g) c =
      wt c • (∑ s, ∑ t, κ s t • pbOp ⟨l, by omega⟩ (F1 s t) c +
        (((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • ∑ s, ∑ t, κ s t • F1 s t c) := by
    rw [Formalism.FourierDecayAlt.P.CutMP.TVG.pbOp_locO ⟨l, by omega⟩ (fun c' hc' => hFN (l + 1) (by omega) c' hc') hc]
    have eF : ∀ c', (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s)
        (rowsNv k r ⟨l + 1, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c' * g)) =
        ∑ s, ∑ t, κ s t • F1 s t c' := by
      intro c'; rw [hF1]
    simp only [eF]
    subst hwt
    beta_reduce
    have hdH : DifferentiableAt ℝ (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c :=
      (has_fderiv_double_sum κ F1 hd1).differentiableAt
    rw [gaugePb r (fun a => Mdim k r a - 1) (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c hc hdH ⟨l, by omega⟩,
      conj_partial_derivative_double_sum κ F1 hd1 ⟨l, by omega⟩ hc]
  rw [hp1, hFN l (by omega) c hc, hFN (l + 1) (by omega) c hc, hFN (l + 2) (by omega) c hc]
  have hpt : ∀ s t, qminorOp (EH k r) (rowsNv k r ⟨l, by omega⟩ s) (rowsNv k r ⟨l, by omega⟩ t)
      (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g) =
      (Y - ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s)
          (rowsNv k r ⟨l + 1, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g) -
        pbOp ⟨l, by omega⟩ (F1 s t) c -
        (star (c ⟨l + 1, by omega⟩) / star (c ⟨l, by omega⟩)) • qminorOp (EH k r) (rowsNv k r ⟨l + 2, by omega⟩ s)
          (rowsNv k r ⟨l + 2, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g) := by
    intro s t
    have h := stepBv_pt z z' hz hz' hDo hN hf hLf hRf hc hg hcg l hl s t (Q.uC k r (Fin.last r) Y - 1)
    rw [hF1, ← uCv_gauge (k := k) l (by omega) Y]
    exact h
  have hL : (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsNv k r ⟨l, by omega⟩ s) (rowsNv k r ⟨l, by omega⟩ t)
      (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g)) =
      ∑ s, ∑ t, κ s t • ((Y - ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r)
          (rowsNv k r ⟨l + 1, by omega⟩ s) (rowsNv k r ⟨l + 1, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J
            (wCell k r (Fin.last r) c * g) -
        pbOp ⟨l, by omega⟩ (F1 s t) c -
        (star (c ⟨l + 1, by omega⟩) / star (c ⟨l, by omega⟩)) • qminorOp (EH k r) (rowsNv k r ⟨l + 2, by omega⟩ s)
          (rowsNv k r ⟨l + 2, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g)) :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [hpt s t]
  have hA : (∑ s, ∑ t, κ s t • F1 s t c) = ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsNv k r ⟨l + 1, by omega⟩ s)
      (rowsNv k r ⟨l + 1, by omega⟩ t) (Q.uC k r (Fin.last r) Y - 1) J (wCell k r (Fin.last r) c * g) := by
    rw [hF1]
  rw [hL, hA]
  exact fin_algv _ _ _ _ _ _ _ _ _

end Formalism.FourierDecayAlt.P.CutMP
