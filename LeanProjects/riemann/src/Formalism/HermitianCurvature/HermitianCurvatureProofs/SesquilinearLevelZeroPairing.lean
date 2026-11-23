import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairLevZeroIndep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section One

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem rrw_one (QQ : ℂ → M2 A) (s0 : S) (Y : ℂ) :
    RRw QQ [(⟨true, s0, Y⟩ : Letter ℂ S)] = ins s0 (lift0 (QQ Y)) := by
  simp [RRw, TTw]

theorem ins_lift0_apply (s0 : S) (M : M2 A) (z z' : Ix S) :
    ins s0 (lift0 M) z z' = if (∀ b, b ≠ s0 → z b = z' b) then M (z s0) (z' s0) else 0 := by
  unfold ins lift0
  simp only [Matrix.sum_apply, Matrix.map_apply]
  have h1 : ∀ (i j : Fin 2), (eU s0 i j * io (M i j) : SlopeTestRemainingChoices S A) z z' =
      if z s0 = i ∧ z' s0 = j ∧ ∀ b, b ≠ s0 → z b = z' b then M i j else 0 := by
    intro i j
    unfold io
    rw [Matrix.mul_apply, Finset.sum_eq_single z']
    · simp only [eU, Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
    · intro b _ hb
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ z') h
  simp only [h1]
  by_cases h : ∀ b, b ≠ s0 → z b = z' b
  · rw [if_pos h, Finset.sum_eq_single (z s0)]
    · rw [Finset.sum_eq_single (z' s0)]
      · rw [if_pos ⟨rfl, rfl, h⟩]
      · intro j _ hj; rw [if_neg]; intro hh; exact hj hh.2.1.symm
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]; intro hh; exact hi hh.1.symm
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; intro hh; exact h hh.2.2

def eS (s0 : S) (i : Fin 2) : Ix S := Function.update (fun _ => 0) s0 i

theorem eS_self (s0 : S) (i : Fin 2) : eS s0 i s0 = i := by simp [eS]

theorem eS_agree (s0 : S) (i j : Fin 2) : ∀ b, b ≠ s0 → eS s0 i b = eS s0 j b := by
  intro b hb; simp [eS, Function.update_of_ne hb]

end One

section ActOne

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem blockMulVec_one_letter (QQ : ℂ → M2 (Q.Pr V)) (s0 : S) (Y : ℂ) (i j : Fin 2) (Φ : V) :
    actP (RRw QQ [(⟨true, s0, Y⟩ : Letter ℂ S)]) (Pi.single (eS s0 j) Φ) (eS s0 i) = (QQ Y i j).1 Φ := by
  rw [rrw_one]
  unfold actP
  rw [Finset.sum_eq_single (eS s0 j)]
  · rw [Pi.single_eq_same, ins_lift0_apply, if_pos (eS_agree s0 i j), eS_self, eS_self]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end ActOne

section Data

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem constant_one_mem_nonvanishing : (fun _ => (1 : ℂ)) ∈ OmX P.r := fun _ => one_ne_zero

theorem act_eq_actP (M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) (x : Ix S → RadSp P.k P.r z z' π π') :
    P5.act M x = actP M x := rfl

theorem wordOK_nil : WordOK P z z' π π' st l0 ([] : List (Letter ℂ S)) := by
  simp [WordOK, Fr.admitted]

theorem form_zero_left' (x : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) :
    form μ 0 (0 : Ix S → RadSp P.k P.r z z' π π') x c = 0 := by
  unfold form
  simp [pairAt_zero_left]

theorem sesqOn_form (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) :
    SesqOn (Submodule.pi Set.univ fun _ : Ix S => K 0) (fun x y => form μ 0 x y (fun _ => 1)) := by
  have h := ((hThm [] wordOK_nil).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing).1
  intro x hx x' hx' y hy a
  have := h x hx x' hx' y hy a
  simpa [RRform, RRi, RRw, act_eq_actP, polyAction_one₂] using this

theorem sesquilinear_level_zero_pairing (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) : SesqCls (K 0) (bet μ) := by
  have hS := sesqOn_form hThm
  let s1 : Ix S := fun _ => 0
  have hsg : ∀ Φ ∈ K 0, Pi.single s1 Φ ∈ Submodule.pi Set.univ fun _ : Ix S => K 0 := by
    intro Φ hΦ b _
    by_cases h : b = s1
    · subst h; simpa using hΦ
    · simp [Pi.single_eq_of_ne h]
  have hb : ∀ Φ Ψ : RadSp P.k P.r z z' π π', bet μ Φ Ψ = form μ 0 (Pi.single s1 Φ) (Pi.single s1 Ψ) (fun _ => 1) := by
    intro Φ Ψ
    rw [form_single_left, Pi.single_eq_same]; rfl
  refine ⟨fun x _ y _ => pairLev_swap _ _ _, fun x hx x' hx' y hy => ?_, fun x hx y hy c => ?_⟩
  · rw [hb, hb, hb, Pi.single_add]
    have := (hS _ (hsg x hx) _ (hsg x' hx') _ (hsg y hy) 1).1
    simpa using this
  · rw [hb, hb, Pi.single_smul]
    have := (hS 0 (Submodule.zero_mem _) _ (hsg x hx) _ (hsg y hy) c).1
    simp only [zero_add] at this
    rw [this, form_zero_left', zero_add]

theorem qq_adj (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (s0 : S) (Y : ℝ)
    (hw : WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)]) (i j : Fin 2)
    (Φ Ψ : RadSp P.k P.r z z' π π') (hΦ : Φ ∈ K 0) (hΨ : Ψ ∈ K 0) :
    bet μ ((QQi L st 0 Y i j).1 Φ) Ψ = bet μ Φ ((QQi L st 0 Y j i).1 Ψ) := by
  obtain ⟨hSq, hNn⟩ := (hThm _ hw).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing
  have hsg : ∀ (s : Ix S) (Φ : RadSp P.k P.r z z' π π'), Φ ∈ K 0 →
      Pi.single s Φ ∈ Submodule.pi Set.univ fun _ : Ix S => K 0 := by
    intro s Φ hΦ b _
    by_cases h : b = s
    · subst h; simpa using hΦ
    · simp [Pi.single_eq_of_ne h]
  have hh := herm_on _ _ hSq hNn (Pi.single (eS s0 j) Φ) (hsg _ _ hΦ) (Pi.single (eS s0 i) Ψ) (hsg _ _ hΨ)
  have ev : ∀ (a b : Fin 2) (Φ Ψ : RadSp P.k P.r z z' π π'),
      RRform L st μ 0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)] (Pi.single (eS s0 b) Φ) (Pi.single (eS s0 a) Ψ)
        (fun _ => 1) = pairLev μ 0 ((QQi L st 0 Y a b).1 Φ) Ψ (fun _ => 1) := by
    intro a b Φ Ψ
    unfold RRform RRi
    rw [form_single_right, act_eq_actP, blockMulVec_one_letter]
  rw [ev, ev] at hh
  unfold bet
  rw [pairLev_swap ((QQi L st 0 (Y : ℂ) j i).1 Ψ) Φ, hh, Complex.conj_conj]

def Gen (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (Pts : Set ℝ) : Set (Pr (RadSp P.k P.r z z' π π')) :=
  {a | ∃ Y ∈ Pts, ∃ i j : Fin 2, a = QQi L st 0 (Y : ℂ) i j}

def Ucls (K0 : Submodule ℂ (RadSp P.k P.r z z' π π')) (G : Set (Pr (RadSp P.k P.r z z' π π'))) :
    Submodule ℂ (RadSp P.k P.r z z' π π') where
  carrier := {Φ | ∀ m ∈ Submonoid.closure G, m.1 Φ ∈ K0}
  add_mem' {Φ Ψ} hΦ hΨ m hm := by rw [map_add]; exact K0.add_mem (hΦ m hm) (hΨ m hm)
  zero_mem' m _ := by rw [map_zero]; exact K0.zero_mem
  smul_mem' c Φ hΦ m hm := by rw [map_smul]; exact K0.smul_mem c (hΦ m hm)

theorem Ucls_le (K0 : Submodule ℂ (RadSp P.k P.r z z' π π')) (G : Set (Pr (RadSp P.k P.r z z' π π'))) :
    Ucls K0 G ≤ K0 := fun Φ hΦ => hΦ 1 (Submonoid.one_mem _)

theorem SesqCls.mono {V : Type} [AddCommGroup V] [Module ℂ V] {U U' : Submodule ℂ V} {β : V → V → ℂ}
    (h : SesqCls U β) (hle : U' ≤ U) : SesqCls U' β :=
  ⟨fun x hx y hy => h.herm x (hle hx) y (hle hy), fun x hx x' hx' y hy => h.add_left x (hle hx) x' (hle hx') y (hle hy),
    fun x hx y hy c => h.smul_left x (hle hx) y (hle hy) c⟩

theorem gen_star (hS : IsStart (QQi L st 0) (M.qC P)) (Pts : Set ℝ) {a : Pr (RadSp P.k P.r z z' π π')}
    (ha : a ∈ Gen L st Pts) : star a ∈ Gen L st Pts := by
  obtain ⟨Y, hY, i, j, rfl⟩ := ha
  refine ⟨Y, hY, j, i, ?_⟩
  have h := hS.herm (Y : ℂ) (Complex.conj_ofReal Y)
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  exact this

theorem gen_mem_adjB (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (hS : IsStart (QQi L st 0) (M.qC P))
    (Pts : Set ℝ) (hPts : ∀ Y ∈ Pts, ∃ s0 : S, WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)])
    {a : Pr (RadSp P.k P.r z z' π π')} (ha : a ∈ Gen L st Pts) :
    a ∈ adjB (Ucls (K 0) (Gen L st Pts)) (bet μ) ((sesquilinear_level_zero_pairing hThm).mono (Ucls_le _ _)) := by
  have hsa := gen_star hS Pts ha
  refine ⟨fun Φ hΦ m hm => ?_, fun Φ hΦ m hm => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · exact hΦ (m * a) (Submonoid.mul_mem _ hm (Submonoid.subset_closure ha))
  · exact hΦ (m * star a) (Submonoid.mul_mem _ hm (Submonoid.subset_closure hsa))
  · obtain ⟨Y, hY, i, j, rfl⟩ := ha
    obtain ⟨s0, hw⟩ := hPts Y hY
    have e : (QQi L st 0 (Y : ℂ) i j).2.unop = (QQi L st 0 (Y : ℂ) j i).1 := by
      have h := hS.herm (Y : ℂ) (Complex.conj_ofReal Y)
      have := congrFun (congrFun h j) i
      rw [Matrix.conjTranspose_apply] at this
      rw [← this]; rfl
    rw [e]
    exact qq_adj hThm s0 Y hw i j Φ Ψ (Ucls_le _ _ hΦ) (Ucls_le _ _ hΨ)

theorem form_zero_eq_position_pairing (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (Y₁ Y₂ : Ix S → RadSp P.k P.r z z' π π')
    (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) : form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  rw [Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ Y₁ Y₂ 0 (fun _ => 1)]
  exact form_eq_pairS μ (K 0) _ (sesqOn_form hThm) Y₁ Y₂ h₁ h₂

theorem jl_mem {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    {𝒜 : StarSubalgebra ℂ A} (L : List (Letter ℂ S)) : (JL L : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  induction L with
  | nil => exact (entSub 𝒜).one_mem
  | cons l L ih =>
    rw [JL]
    refine (entSub 𝒜).mul_mem (ins_mem _ ?_) ih
    split_ifs
    · exact symplectic_form_mem_entrywise
    · exact entries_mem_transpose symplectic_form_mem_entrywise

theorem dk_radial {X : ActualOps P.k P.r z z' π π'} (hD : IsData P z z' π π' X μ L st l0)
    (hThm : ThmPOn (S := S) P z z' π π' μ L st K l0) (Pts : Set ℝ)
    (hPts : ∀ Y ∈ Pts, ∃ s0 : S, WordOK P z z' π π' st l0 [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ S)])
    (w Lw : List (Letter ℂ S)) (hDK : FormPairingAction.DKHyp (M.qC P) w Lw)
    (hOK1 : WordOK P z z' π π' st l0 (Lw ++ w)) (hOK2 : WordOK P z z' π π' st l0 (Lw.map dl ++ w))
    (hP1 : ∀ l ∈ Lw ++ w, ∃ Y ∈ Pts, l.pt = (Y : ℂ)) (hP2 : ∀ l ∈ Lw, ∃ Y ∈ Pts, l.pt + 1 = (Y : ℂ))
    (X₁ X₂ : Ix S → RadSp P.k P.r z z' π π') (h1 : ∀ e, X₁ e ∈ Ucls (K 0) (Gen L st Pts))
    (h2 : ∀ e, X₂ e ∈ Ucls (K 0) (Gen L st Pts)) :
    (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0).im = 0 ∧
    0 ≤ (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0).re ∧
    (form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0).im = 0 ∧
    0 ≤ (form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0).re ∧
    ‖pairS (bet μ) (actP (JL Lw * RRw (QQi L st 0) w) X₁) X₂‖ ^ 2 ≤
      (form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0 *
        form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0 /
        (Lw.map fun l => qw (M.qC P) w l.pt).prod).re := by
  have hS := isStart_QQi P z z' π π' X μ L st l0 hD 0
  have hK := sesquilinear_level_zero_pairing hThm
  have hle := Ucls_le (K 0) (Gen L st Pts)
  have hU := hK.mono hle
  have hGen : ∀ Y ∈ Pts, ∀ i j, QQi L st 0 (Y : ℂ) i j ∈ adjB _ (bet μ) hU := fun Y hY i j =>
    gen_mem_adjB hThm hS Pts hPts ⟨Y, hY, i, j, rfl⟩
  have hat : ∀ Y : ℂ, (∃ Y' ∈ Pts, Y = (Y' : ℂ)) → ∀ i j, QQi L st 0 Y i j ∈ adjB _ (bet μ) hU := by
    rintro Y ⟨Y', hY', rfl⟩ i j; exact hGen Y' hY' i j
  have hPs : Ps (QQi L st 0) (M.qC P) w Lw ∈ entSub (adjB _ (bet μ) hU) := by
    refine ps_mem_at _ _ _ _ fun l hl a b => ⟨fun _ => hat _ (hP2 l hl) a b, fun hneg => ?_⟩
    have := hDK.1 l hl
    rw [this] at hneg; exact absurd hneg (by decide)
  have hRRe : RRw (QQi L st 0) (Lw ++ w) ∈ entSub (adjB _ (bet μ) hU) :=
    rrw_mem_at _ _ fun l hl a b => hat _ (hP1 l hl) a b
  have hRRe2 : RRw (QQi L st 0) (Lw.map dl ++ w) ∈ entSub (adjB _ (bet μ) hU) := by
    refine rrw_mem_at _ _ fun l hl a b => hat _ ?_ a b
    rcases List.mem_append.mp hl with h | h
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
      have hp := hDK.1 l' hl'
      obtain ⟨Y, hY, e⟩ := hP2 l' hl'
      refine ⟨Y, hY, ?_⟩
      simp [dl, hp, e]
    · exact hP1 l (List.mem_append_right _ h)
  have hRRw : RRw (QQi L st 0) w ∈ entSub (adjB _ (bet μ) hU) :=
    rrw_mem_at _ _ fun l hl a b => hat _ (hP1 l (List.mem_append_right _ hl)) a b
  have hJR : JL Lw * RRw (QQi L st 0) w ∈ entSub (adjB _ (bet μ) hU) := (entSub _).mul_mem (jl_mem Lw) hRRw
  have pres : ∀ {M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))}, M ∈ entSub (adjB _ (bet μ) hU) →
      ∀ a b, ∀ x ∈ Ucls (K 0) (Gen L st Pts), (M a b).1 x ∈ Ucls (K 0) (Gen L st Pts) :=
    fun hM a b x hx => (hM a b).1 x hx
  have hSq := sesqOn_form (S := S) hThm
  have conv : ∀ (Y₁ Y₂ : Ix S → RadSp P.k P.r z z' π π'), InU (Ucls (K 0) (Gen L st Pts)) Y₁ →
      InU (Ucls (K 0) (Gen L st Pts)) Y₂ → form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
    intro Y₁ Y₂ hY₁ hY₂
    rw [Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ Y₁ Y₂ 0 (fun _ => 1)]
    exact form_eq_pairS μ (K 0) _ hSq Y₁ Y₂ (fun a => hle (hY₁ a)) (fun a => hle (hY₂ a))
  have posOf : ∀ u : List (Letter ℂ S), WordOK P z z' π π' st l0 u →
      RRw (QQi L st 0) u ∈ entSub (adjB _ (bet μ) hU) → ∀ Y : Ix S → RadSp P.k P.r z z' π π',
      InU (Ucls (K 0) (Gen L st Pts)) Y →
      0 ≤ (pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y).re ∧ (pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y).im = 0 := by
    intro u hu hM Y hY
    have hn := ((hThm u hu).2.2 0 (fun _ => 1) constant_one_mem_nonvanishing).2 Y (fun a _ => hle (hY a))
    have e : RRform L st μ 0 u Y Y (fun _ => 1) = pairS (bet μ) (actP (RRw (QQi L st 0) u) Y) Y :=
      form_eq_pairS μ (K 0) _ hSq _ _ (fun a => hle (blockMulVec_apply_mem (pres hM) hY a)) (fun a => hle (hY a))
    beta_reduce at hn
    rw [e] at hn
    exact ⟨(Complex.nonneg_iff.mp hn).1, (Complex.nonneg_iff.mp hn).2.symm⟩
  have hPos := posOf _ hOK1 hRRe
  have hPos2 := posOf _ hOK2 hRRe2 X₂ h2
  have dk := dk_partial hU (QQi L st 0) (M.qC P) w Lw hS hDK hPs (pres hRRe) hPos X₁ X₂ h1 h2
  have hP1' := hPos X₁ h1
  have eA : form μ 0 (P5.act (RRi L st 0 (Lw ++ w)) X₁) X₁ 0 = pairS (bet μ) (actP (RRw (QQi L st 0) (Lw ++ w)) X₁) X₁ :=
    conv _ _ (blockMulVec_apply_mem (pres hRRe) h1) h1
  have eB : form μ 0 (P5.act (RRi L st 0 (Lw.map dl ++ w)) X₂) X₂ 0 =
      pairS (bet μ) (actP (RRw (QQi L st 0) (Lw.map dl ++ w)) X₂) X₂ :=
    conv _ _ (blockMulVec_apply_mem (pres hRRe2) h2) h2
  rw [eA, eB]
  exact ⟨hP1'.2, hP1'.1, hPos2.2, hPos2.1, dk.2⟩

end Data

end

end Formalism.FourierDecayAlt.P.PBF
