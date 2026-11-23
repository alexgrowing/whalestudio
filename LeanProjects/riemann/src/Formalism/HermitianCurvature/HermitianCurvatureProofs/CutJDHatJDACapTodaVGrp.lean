import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem pbN_locO (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbN r i f₁ c = pbN r i f₂ c := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_locO _ h hc
  · rfl

theorem iteratedOperator_eqOn_of_eqOn (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (kvP r w m).1 f₁ c = (kvP r w m).1 f₂ c ∧ (kvP r w m).2 f₁ c = (kvP r w m).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | m + 1, f₁, f₂, h, c, hc => by
    have hin : ∀ c' ∈ OmX r, (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c' =
        (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c' := fun c' hc' => by
      rw [h c' hc', pbN_locO _ h hc']
    have ih1 := iteratedOperator_eqOn_of_eqOn w m _ _ hin
    have ih2 := iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h
    refine ⟨?_, (ih2 c hc).1⟩
    show (kvP r w m).1 _ c - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₁)) c =
      (kvP r w m).1 _ c - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₂)) c
    rw [(ih1 c hc).1]
    congr 1
    unfold cbN cbiN
    split_ifs <;> simp [cbOp, cbiOp, (ih2 c hc).2]

theorem kvC_loc (w : ℂ) (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : kvC r w m f₁ c = kvC r w m f₂ c := (iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h c hc).1

theorem kvC_zero (w : ℂ) (f : (Fin r → ℂ) → X) : kvC r w 0 f = f := rfl

theorem kvC_one (w : ℂ) (f : (Fin r → ℂ) → X) (hr : 1 ≤ r) (c : Fin r → ℂ) :
    kvC r w 1 f c = w • f c - pbOp ⟨r - 1, by omega⟩ f c := by
  show (w - ((0 : ℕ) : ℂ)) • f c - pbN r (r - 0 - 1) f c - cbN r (r - 0) (cbiN r (r - 0 - 1) (fun _ => 0)) c = _
  have h1 : r - 0 - 1 = r - 1 := by omega
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
  unfold pbN cbN
  rw [dif_pos (by omega), dif_neg (lt_irrefl r)]
  simp

theorem kvC_two (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) (c : Fin r → ℂ) :
    kvC r w (m + 2) f c = kvC r w (m + 1) (fun c => (w - ((m + 1 : ℕ) : ℂ)) • f c - pbN r (r - (m + 1) - 1) f c) c -
      cbN r (r - (m + 1)) (cbiN r (r - (m + 1) - 1) (kvC r w m f)) c := rfl

end loc

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

abbrev TorV (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, l.val < j ∧ x = EA hD (esI k r l) (esI k r l)}

theorem comm_TorV (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, l.val < j → p ≠ esI k r l) (hq : ∀ l : Fin r, l.val < j → q ≠ esI k r l) (P : SA E hD)
    (hP : P ∈ TorV hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (esI k r l) (esI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem TorV_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : TorV (E := E) hD j ≤ TorV hD j' := Algebra.adjoin_mono fun x ⟨l, hl, hx⟩ => ⟨l, lt_of_lt_of_le hl h, hx⟩

theorem EAs_mem_TorV (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : l.val < j) :
    EA (E := E) hD (esI k r l) (esI k r l) ∈ TorV hD j := Algebra.subset_adjoin ⟨l, h, rfl⟩

theorem esI_ne {a b : Fin r} (h : a.val ≠ b.val) : esI k r a ≠ esI k r b := by
  intro h'
  have h2 := congrArg Fin.val h'
  simp only [esI] at h2
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem root_action_on_truncated_vector (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleEv)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : b.val < a.val) :
    ((EA hD (esI k r a) (esI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (esI k r a)) (cI (esI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (esI k r a) (esI k r b) (cut k r 0 D f) g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

theorem la_torus (hD : IsOpen D) (hTC : TorusCellv) (v₀ : VS k r 0 D E) (g₀ : Mx k r)
    (hg₀ : g₀ ∈ Glev k r (Fin.last r)) (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (l : Fin r) (w' : ℂ) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    La hD v₀ (wCell k r (Fin.last r) c * g₀) (Tm (EA hD) w' (esI k r l) (esI k r l) * x) =
      w' • La hD v₀ (wCell k r (Fin.last r) c * g₀) x -
        pbOp l (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) x) c := by
  have hγ := hcell c hc
  rw [La_apply, La_apply]
  simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
    Submodule.coe_add, Pi.add_apply, ite_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
    Submodule.coe_smul, Pi.smul_apply]
  rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D _ hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l,
    sub_eq_add_neg]
  rfl

end alg

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem claimV (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion)
    (hD : IsOpen D) (v₀ : VS k r 0 D E) (g₀ : Mx k r) (w : ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D) :
    ∀ (m : ℕ), m ≤ r → ∀ P ∈ TorV hD (r - m), ∀ c ∈ OmX r,
      La hD v₀ (wCell k r (Fin.last r) c * g₀) (qminor (EA hD) (colsVm k r m) (colsVm k r m) w * P) =
        kvC r w m (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) P) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [MC.qminor_zero, one_mul]
    rfl
  · rw [MC.qminor_one]
    have hx0 : colsVm k r 1 0 = esI k r ⟨r - 1, by omega⟩ := by
      ext
      simp only [colsVm, esI, Fin.val_zero]
      omega
    rw [hx0, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - 1, by omega⟩ w P c hc, kvC_one w _ hm c]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ TorV hD (r - (m + 1)) := TorV_mono hD (by omega) hP
    have hP0 : P ∈ TorV hD (r - m) := TorV_mono hD (by omega) hP
    set ρ : ℂ := star (c ⟨r - m - 1, by omega⟩) / star (c ⟨r - m - 2, by omega⟩) with hρ
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ a : Fin r, r - m - 2 ≤ a.val → ∀ l' : Fin r, l'.val < r - (m + 2) → esI k r a ≠ esI k r l' :=
      fun a ha l' hl' => esI_ne (by omega)
    have hR0 : ∀ (x : SA E hD) (a : Fin r), r - m - 1 < a.val →
        LaP (x * EA hD (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0 := by
      intro x a ha
      rw [hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot a (by omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf a ⟨r - m - 2, by omega⟩ (by simp only; omega), if_neg (by simp only; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD,
        LaP (x * EA hD (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot ⟨r - m - 1, by omega⟩ (by simp only; omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul,
        Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf ⟨r - m - 1, by omega⟩ ⟨r - m - 2, by omega⟩ (by simp only; omega),
        if_pos (by simp only; omega), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (b : Fin r), r - m - 2 < b.val →
        LaP (EA hD (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) =
          (if b.val = r - m - 1 then ρ else 0) • LaP x := by
      intro x b hb
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 b ⟨r - m - 2, by omega⟩ (by simp only; omega)]
      congr 1
      by_cases hbm : b.val = r - m - 1
      · have hb' : b = ⟨r - m - 1, by omega⟩ := Fin.ext hbm
        rw [if_pos (by simp only; omega), if_pos hbm, hρ, congrArg c hb']
      · rw [if_neg (by simp only; omega), if_neg hbm]
    have hX := hCh (SA E hD) E k r (EA (E := E) hD) LaP ρ (EA_gl (E := E) hD) m hm2 w hR0 hR1 hL
    set T := Tm (EA (E := E) hD) (w - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩)
      (esI k r ⟨r - m - 2, by omega⟩) with hT
    have hTmem : T ∈ TorV hD (r - (m + 1)) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EAs_mem_TorV hD ⟨r - m - 2, by omega⟩ (by simp only; omega))
    have hTP : T * P ∈ TorV hD (r - (m + 1)) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc
    rw [hLaP_apply, hLaP_apply, hLaP_apply, mul_assoc] at hX
    rw [hX, ih1, ih0, kvC_two]
    have hloc := kvC_loc w (m + 1) (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) (T * P))
      (fun c' => (w - ((m + 1 : ℕ) : ℂ)) • La hD v₀ (wCell k r (Fin.last r) c' * g₀) P -
        pbN r (r - (m + 1) - 1) (fun c'' => La hD v₀ (wCell k r (Fin.last r) c'' * g₀) P) c')
      (fun c' hc' => by
        rw [hT, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - m - 2, by omega⟩ _ P c' hc']
        unfold pbN
        rw [dif_pos (by omega)]
        have e : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e]) hc
    rw [hloc]
    congr 1
    unfold cbN cbiN
    rw [dif_pos (by omega), dif_pos (by omega)]
    have e1 : (⟨r - (m + 1), by omega⟩ : Fin r) = ⟨r - m - 1, by omega⟩ := Fin.ext (by simp only; omega)
    have e2 : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e1, e2]
    simp only [cbOp, cbiOp, hρ, div_eq_mul_inv, mul_smul]

end claim

end Formalism.FourierDecayAlt.P.CutMP.TVG
