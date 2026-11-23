import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem pairJ_rel {X Y : Type} {w : List C.Letter} (R : X → Y → Prop) (c : ℂ)
    (Ξ1 : (Ix (Fin w.length) → X) → (Ix (Fin w.length) → X) → ℂ)
    (Ξ2 : (Ix (Fin w.length) → Y) → (Ix (Fin w.length) → Y) → ℂ)
    (h : ∀ x x' y y', (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → Ξ1 x x' = c * Ξ2 y y') :
    ∀ (ys : List ℝ) (x : Ix (Fin (KB.plusW ys w).length) → X) (x' : Ix (Fin (KB.minusW ys w).length) → X)
      (y : Ix (Fin (KB.plusW ys w).length) → Y) (y' : Ix (Fin (KB.minusW ys w).length) → Y),
      (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → KB.pairJ Ξ1 ys x x' = c * KB.pairJ Ξ2 ys y y'
  | [], x, x', y, y', hx, hx' => h x x' y y' hx hx'
  | _ :: ys, x, x', y, y', hx, hx' => by
    show KB.pairJ Ξ1 ys _ _ - KB.pairJ Ξ1 ys _ _ = c * (KB.pairJ Ξ2 ys _ _ - KB.pairJ Ξ2 ys _ _)
    have a1 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 1 e)) (fun e => x' (Fin.cons 0 e))
      (fun e => y (Fin.cons 1 e)) (fun e => y' (Fin.cons 0 e)) (fun e => hx _) (fun e => hx' _)
    have a2 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 0 e)) (fun e => x' (Fin.cons 1 e))
      (fun e => y (Fin.cons 0 e)) (fun e => y' (Fin.cons 1 e)) (fun e => hx _) (fun e => hx' _)
    exact (congrArg₂ (· - ·) a1 a2).trans (mul_sub _ _ _).symm

theorem prod_real (zs : List ℂ) (h : ∀ z ∈ zs, z.im = 0) : zs.prod.im = 0 ∧ zs.prod.re = (zs.map Complex.re).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨h1, h2⟩ := ih fun z' hz' => h z' (by simp [hz'])
    simp only [List.prod_cons, List.map_cons, Complex.mul_im, Complex.mul_re, hz, h1, mul_zero, zero_mul,
      add_zero, sub_zero, h2]
    exact ⟨trivial, trivial⟩

theorem form_castIx {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {n m : ℕ} (h : n = m) (U V : Ix (Fin n) → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (fun z => U (z ∘ Fin.cast h)) (fun z => V (z ∘ Fin.cast h)) c = form μ 0 U V c := by
  subst h
  rfl

theorem form_embed {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (ι : Ix S' → Ix S)
    (hι : Function.Injective ι) (x y : Ix S' → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Function.extend ι x 0) (Function.extend ι y 0) c = form μ 0 x y c := by
  unfold form
  congr 1
  funext c'
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, pairAt_zero_left]

theorem pairS_embed {V : Type} [AddCommGroup V] [Module ℂ V] {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S']
    [DecidableEq S'] (β : V → V → ℂ) (hβ : ∀ v, β 0 v = 0) (ι : Ix S' → Ix S) (hι : Function.Injective ι)
    (x y : Ix S' → V) : pairS β (Function.extend ι x 0) (Function.extend ι y 0) = pairS β x y := by
  unfold pairS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hβ]

def ixEmb {m n : ℕ} (h : m ≤ n) (e : Ix (Fin m)) : Ix (Fin n) := fun t => if ht : t.val < m then e ⟨t, ht⟩ else 0

theorem ixEmb_inj {m n : ℕ} (h : m ≤ n) : Function.Injective (ixEmb h) := by
  intro e e' he
  funext t
  have := congrFun he ⟨t.val, by omega⟩
  simpa [ixEmb, t.isLt] using this

theorem bet_neg {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v v' : RadSp k r z z' π π') : bet μ (-v) v' = -bet μ v v' := by
  unfold bet
  have := pairLev_smul_left (μ := μ) (i := 0) v v' (fun _ => 1) (-1)
  have e : ((-1 : ℂ) • v) = -v := neg_one_smul ℂ v
  rw [e, neg_one_mul] at this
  exact this

theorem bet_zero {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v : RadSp k r z z' π π') : bet μ 0 v = 0 := by
  unfold bet; exact pairLev_zero_left v _

section EmbData

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ}
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem form_zero_eq_position_pairing_of_le (hThm : ThmPOn (S := Fin n) P z z' π π' μ L st K l0) {m : ℕ} (hmn : m ≤ n)
    (Y₁ Y₂ : Ix (Fin m) → RadSp P.k P.r z z' π π') (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) :
    form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  have extK : ∀ v : Ix (Fin m) → RadSp P.k P.r z z' π π', (∀ a, v a ∈ K 0) →
      ∀ z, Function.extend (ixEmb hmn) v 0 z ∈ K 0 := by
    intro v hv z
    by_cases hz : ∃ a, ixEmb hmn a = z
    · obtain ⟨a, rfl⟩ := hz
      rw [(ixEmb_inj hmn).extend_apply]; exact hv a
    · rw [Function.extend_apply' _ _ _ hz]; exact (K 0).zero_mem
  have e1 := form_embed μ (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂ 0
  have e2 := form_zero_eq_position_pairing hThm (Function.extend (ixEmb hmn) Y₁ 0) (Function.extend (ixEmb hmn) Y₂ 0)
    (extK _ h₁) (extK _ h₂)
  have e3 := pairS_embed (V := RadSp P.k P.r z z' π π') (bet μ) (fun v => bet_zero μ v) (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂
  exact e1.symm.trans (e2.trans e3)

end EmbData

theorem final_ineq (Cst : ℝ) (A B P0 Q : ℂ) (qs : List ℂ) (hQ : Q = qs.prod)
    (hqs : ∀ z ∈ qs, 0 < z.re ∧ z.im = 0) (hAi : A.im = 0) (hBi : B.im = 0) (hdk : ‖P0‖ ^ 2 ≤ (A * B / Q).re) :
    ‖(Cst : ℂ) * P0‖ ^ 2 * (qs.map Complex.re).prod ≤ ((Cst : ℂ) * A).re * ((Cst : ℂ) * B).re := by
  obtain ⟨hQi, hQr⟩ := prod_real qs fun z hz => (hqs z hz).2
  have hpos : 0 < (qs.map Complex.re).prod := List.prod_pos fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact (hqs z hz).1
  have eA : A = (A.re : ℂ) := Complex.ext (by simp) (by simp [hAi])
  have eB : B = (B.re : ℂ) := Complex.ext (by simp) (by simp [hBi])
  have eQ : Q = ((qs.map Complex.re).prod : ℂ) := by
    rw [hQ]; exact Complex.ext (by simp [hQr]) (by simp [hQi])
  have h1 : (A * B / Q).re = A.re * B.re / (qs.map Complex.re).prod := by
    rw [eA, eB, eQ, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  rw [h1, le_div_iff₀ hpos] at hdk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow, sq_abs]
  nlinarith [sq_nonneg Cst]

theorem cast_map_pred {n m : ℕ} (h : n = m) (Q : ∀ k, List (Letter ℂ (Fin k)) → Prop) (u : List (Letter ℂ (Fin n)))
    (hu : Q n u) : Q m (u.map (castL h)) := by
  subst h; rwa [castL_rfl]

theorem Lw_qw (q : ℂ → ℂ) (ys : List ℝ) (w : List C.Letter) :
    ((Lw ys w).map fun l => qw q (Ww ys w) l.pt) = ys.map fun y : ℝ => qw q (D.positionted w) (y : ℂ) := by
  apply List.ext_getElem
  · simp [Lw_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, Lw_getElem, qw_Ww]

theorem pb_sizeStd_main : Formalism.FourierDecayAlt.KB.SizeStd := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w ys hc1 hc2 hys
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  have hqpos := qw_pos P hOK p.l0 hl1 hlk w ys hc1 hc2
  refine ⟨fun y hy => (hqpos y hy).1, ?_⟩
  intro x x' ε hε hx hx'
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin (KB.plusW ys w).length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hJ' : PicsIn p.T jF (K 0) := hJ

  choose Φ hΦK hΦ using fun a => hJ (x a) ε hε (hx a).2.1 (hx a).2.2
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) ε hε (hx' a).2.1 (hx' a).2.2

  let Pts : Set ℝ := {Y | (∃ l ∈ KB.plusW ys w, l.2 = Y) ∨ (∃ l ∈ KB.minusW ys w, l.2 = Y)}
  have hW1 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.plusW ys w)
    hc1.1 hc1.2
  have hW2 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.minusW ys w)
    hc2.1 hc2.2
  have hPts : ∀ Y ∈ Pts, ∃ s0 : Fin (KB.plusW ys w).length,
      WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
        [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ (Fin (KB.plusW ys w).length))] := by
    intro Y hY
    have hn : 0 < (KB.plusW ys w).length ∧ I.OnCut P.u P.u' p.l0 Y := by
      rcases hY with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · exact ⟨List.length_pos_of_mem hl, cutWord_mem P hc1 hl⟩
      · exact ⟨by rw [← len_pm]; exact List.length_pos_of_mem hl, cutWord_mem P hc2 hl⟩
    refine ⟨⟨0, hn.1⟩, wordOK_gen (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 _ (by simp)
      (fun l hl => ⟨Y, by simp at hl; rw [hl], hn.2⟩) (by simp)⟩
  have hΦU : ∀ e, Φ e ∈ Ucls (K 0) (Gen L st Pts) := fun e => pic_mem_Ucls hD hJ' Pts hε (hx e) (Φ e) (hΦ e)
  have hΦ'U : ∀ e, Φ' e ∈ Ucls (K 0) (Gen L st Pts) := fun e =>
    pic_mem_Ucls hD hJ' Pts hε (hx' e) (Φ' e) (hΦ' e)

  have hS := isStart_QQi _ _ _ _ _ X μ L st p.l0 hD 0
  have hle := Ucls_le (K 0) (Gen L st Pts)
  have hU := (sesquilinear_level_zero_pairing hThm).mono hle

  have hP1 : ∀ l ∈ Lw ys w ++ Ww ys w, ∃ Y ∈ Pts, l.pt = (Y : ℂ) := by
    intro l hl
    rw [Lw_append_Ww] at hl
    unfold D.positionted at hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨((KB.plusW ys w).get a).2, Or.inl ⟨_, List.get_mem _ _, rfl⟩, rfl⟩
  have hLmem : ∀ l ∈ Lw ys w, ∃ y ∈ ys, l.pt = (y : ℂ) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    rw [Lw_getElem]
    exact ⟨_, List.getElem_mem _, rfl⟩
  have hP2 : ∀ l ∈ Lw ys w, ∃ Y ∈ Pts, l.pt + 1 = (Y : ℂ) := by
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    refine ⟨y + 1, Or.inr ⟨(false, y + 1), ?_, rfl⟩, by rw [e]; push_cast; ring⟩
    rw [minusW_eq]
    exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)
  have hOK1 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      (Lw ys w ++ Ww ys w) := by rw [Lw_append_Ww]; exact hW1
  have hOK2 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      ((Lw ys w).map dl ++ Ww ys w) := by
    rw [Lw_dual]
    exact cast_map_pred (len_pm ys w) (fun k u => WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π' st p.l0 u) _ hW2
  have hDK : FormPairingAction.DKHyp (M.qC (JC.parLev P jF)) (Ww ys w) (Lw ys w) := by
    refine ⟨Lw_plus ys w, good_of_adm st _ hOK1.1, good_of_adm st _ hOK2.1, Lw_pairwise w ys hys, ?_⟩
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    rw [e, qw_Ww]
    intro h0
    have := (hqpos y hy).1
    rw [show qw (M.qC P) (D.positionted w) (y : ℂ) = qw (M.qC (JC.parLev P jF)) (D.positionted w) (y : ℂ) from rfl, h0] at this
    simp at this
  have dk := dk_radial hD hThm Pts hPts (Ww ys w) (Lw ys w) hDK hOK1 hOK2 hP1 hP2 Φ
    (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) hΦU (fun e => hΦ'U _)

  have hRRw : RRw (QQi L st 0) (D.positionted w) ∈ entSub (adjB (Ucls (K 0) (Gen L st Pts)) (bet μ) hU) := by
    refine rrw_mem_at _ _ fun l hl a b => ?_
    unfold D.positionted at hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    refine gen_mem_adjB hThm hS Pts hPts ⟨(w.get i).2, Or.inl ⟨w.get i, ?_, rfl⟩, a, b, rfl⟩
    rw [plusW_eq]; exact List.mem_append_right _ (List.get_mem _ _)
  have hodd := bet_neg (k := (JC.parLev P jF).k) (r := (JC.parLev P jF).r) (z := (p.T.bs jF).z)
    (z' := (p.T.bs jF).z') (π := (p.T.bs jF).π) (π' := (p.T.bs jF).π') μ
  have hmn : w.length ≤ (KB.plusW ys w).length := by rw [len_plusW]; omega
  have ePlus := hform (KB.plusW ys w) x x Φ Φ ε hε hx hx hΦ hΦ
  have eMinus := hform (KB.minusW ys w) x' x' Φ' Φ' ε hε hx' hx' hΦ' hΦ'
  have ePJ := pairJ_rel (w := w) (fun F Ψ => JC.NiceCoef (p.T.bs jF) ε F ∧ IsPic p.T jF Ψ F) (Cst : ℂ)
    (p.form j hj w) (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun u u' v v' hu hu' => hform w u u' v v' ε hε (fun e => (hu e).1) (fun e => (hu' e).1) (fun e => (hu e).2)
      (fun e => (hu' e).2)) ys x x' Φ Φ' (fun e => ⟨hx e, hΦ e⟩) (fun e => ⟨hx' e, hΦ' e⟩)
  have eXi := pairJ_rel (w := w) (fun a b => a = b ∧ a ∈ Ucls (K 0) (Gen L st Pts)) (1 : ℂ)
    (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun x x' => ∑ e, bet μ (actP (RRw (QQi L st 0) (D.positionted w)) x e) (x' e))
    (fun u u' v v' hu hu' => by
      have e1 : u = v := funext fun e => (hu e).1
      have e2 : u' = v' := funext fun e => (hu' e).1
      subst e1 e2
      rw [one_mul]
      have hin : InU (Ucls (K 0) (Gen L st Pts)) (actP (RRw (QQi L st 0) (D.positionted w)) u) :=
        blockMulVec_apply_mem (fun a b x hx => (hRRw a b).1 x hx) (fun e => (hu e).2)
      exact form_zero_eq_position_pairing_of_le hThm hmn _ _ (fun a => hle (hin a)) (fun a => hle (hu' a).2))
    ys Φ Φ' Φ Φ' (fun e => ⟨rfl, hΦU e⟩) (fun e => ⟨rfl, hΦ'U e⟩)
  have ePosition := position_pair (V := RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
    (p.T.bs jF).π (p.T.bs jF).π') (bet μ) hodd (QQi L st 0) w ys Φ Φ'
  have eA : form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.plusW ys w))) Φ) Φ 0 := by rw [Lw_append_Ww]
  have eB : form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.minusW ys w))) Φ') Φ' 0 := by
    rw [Lw_dual]
    show form μ 0 (actP (RRw (QQi L st 0) ((D.positionted (KB.minusW ys w)).map (castL (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w)))) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 = _
    have hc := blockMulVec_cast (QQi L st 0) (len_pm ys w) (D.positionted (KB.minusW ys w)) Φ'
    exact (congrArg (fun V => form μ 0 V (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0) hc).trans
      (form_castIx μ (len_pm ys w) _ _ 0)

  obtain ⟨hAi, -, hBi, -, hdk⟩ := dk
  have ePlus' : p.form j hj (KB.plusW ys w) x x =
      (Cst : ℂ) * form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 := ePlus.trans (congrArg _ eA.symm)
  have eMinus' : p.form j hj (KB.minusW ys w) x' x' = (Cst : ℂ) *
      form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
        (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 := eMinus.trans (congrArg _ eB.symm)
  have hPJ : KB.pairJ (p.form j hj w) ys x x' = (Cst : ℂ) *
      pairS (bet μ) (actP (JL (Lw ys w) * RRw (QQi L st 0) (Ww ys w)) Φ) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) :=
    ePJ.trans (congrArg (fun t => (Cst : ℂ) * t) (eXi.trans ((one_mul _).trans ePosition.symm)))
  have hQ : ((Lw ys w).map fun l => qw (M.qC (JC.parLev P jF)) (Ww ys w) l.pt).prod =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).prod := congrArg List.prod (Lw_qw _ ys w)
  have hre : (ys.map fun y : ℝ => (qw (M.qC P) (D.positionted w) (y : ℂ)).re) =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).map Complex.re := by
    rw [List.map_map]; rfl
  rw [hPJ, ePlus', eMinus', hre]
  refine final_ineq Cst _ _ _ _ _ hQ (fun z hz => ?_) hAi hBi hdk
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact hqpos y hy

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

theorem list_duality_level_group : Formalism.FourierDecayAlt.KB.SizeStd := PBF.pb_sizeStd_main

end Formalism.FourierDecayAlt.P
