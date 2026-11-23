import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section abs
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

noncomputable def cmTiePL (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) :
    Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  ∑ l ∈ range (o + 1),
    (((-1 : ℚ_[p]) ^ l) / (((l.factorial : ℚ_[p]) ^ 2) * ((o + n + r + z - 1).choose l : ℚ_[p]))) •
      ((tieEh w e zv sv) ^ l * ((tieF w e) ^ l * LinearMap.mulLeft ℚ_[p] (X zv ^ z)))

theorem cm_tiePL_apply (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    cmTiePL w e zv sv o n z x = tieP w e zv sv o n z x := by
  simp only [cmTiePL, tieP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.mulLeft_apply]

theorem cm_F_F {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) :
    Commute (tieF (k := ℚ_[p]) w' e') (tieF w e) := by
  unfold tieF
  refine Commute.sum_left _ _ _ (fun c _ => Commute.sum_right _ _ _ (fun d _ => ?_))
  simp only [← Module.End.mul_eq_comp]
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
    exact PhiIntegrality.commute_pderiv _ _

theorem cm_F_mul {r' : ℕ} (w' e' : Fin r' → σ) (q : MvPolynomial σ ℚ_[p]) (hw : ∀ c, pderiv (w' c) q = 0)
    (he : ∀ c, pderiv (e' c) q = 0) : Commute (tieF w' e') (LinearMap.mulLeft ℚ_[p] q) :=
  LinearMap.ext fun f => by
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
    exact tieF_mul_free w' e' q f hw he

theorem cm_F_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) :
    Commute (tieF (k := ℚ_[p]) w' e') (cmTiePL w e zv sv o n z) := by
  unfold cmTiePL
  refine Commute.sum_right _ _ _ (fun l _ => Commute.smul_right ?_ _)
  refine Commute.mul_right (Commute.pow_right ?_ _) (Commute.mul_right (Commute.pow_right (cm_F_F _ _ _ _) _) ?_)
  · exact cm_F_mul w' e' (ehP w e zv sv)
      (fun c => free_ehP (hw c).1 (hw c).2.1 (hw c).2.2.1 (hw c).2.2.2)
      (fun c => free_ehP (he c).1 (he c).2.1 (he c).2.2.1 (he c).2.2.2)
  · exact cm_F_mul w' e' _ (fun c => free_pow (free_X (hw c).1) _) (fun c => free_pow (free_X (he c).1) _)

theorem cm_Fpow_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) (m : ℕ)
    (x : MvPolynomial σ ℚ_[p]) :
    (tieF w' e' ^ m) (tieP w e zv sv o n z x) = tieP w e zv sv o n z ((tieF w' e' ^ m) x) := by
  have h := (cm_F_P (p := p) w' e' w e zv sv o n z hw he).pow_left m
  have h2 := LinearMap.congr_fun h.eq x
  simpa only [Module.End.mul_apply, cm_tiePL_apply] using h2

end abs

section block
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

noncomputable def cmPLL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (L : List (Fin D.T.t))
    (j : Fin D.T.t → ℕ) (jp : ℕ) : Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  L.foldr (fun i acc => cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) * acc) 1

theorem cm_PLL_apply (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : cmPLL p D L j jp x = PL p D L j jp x := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have h1 : cmPLL (r := r) p D (i :: L) j jp = cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
        ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
        (D.T.z i) * cmPLL p D L j jp := rfl
    rw [h1, Module.End.mul_apply, ih, cm_tiePL_apply]
    rfl

noncomputable def cmPplusL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (jp : ℕ) :
    Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  cmTiePL (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus

theorem cm_PplusL_apply (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    cmPplusL p D jp x = Pplus p D jp x := by
  unfold cmPplusL
  rw [cm_tiePL_apply]
  rfl

theorem cm_wv_wv (hB : D.BlockOK) {i k : Fin D.T.t} (h : i ≠ k) (c d : Fin r) : wv D i d ≠ wv D k c := by
  intro h'
  simp only [wv, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_pos_val hB] at this
  exact h (pos_inj hB this)

theorem cm_ev_ev (hB : D.BlockOK) {i k : Fin D.T.t} (h : i ≠ k) (c d : Fin r) : ev D i d ≠ ev D k c := by
  intro h'
  simp only [ev, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_succ_val hB, finPos_succ_val hB] at this
  exact h (pos_inj hB (by omega))

theorem cm_wv_ev (hB : D.BlockOK) (i k : Fin D.T.t) (c d : Fin r) : wv D i d ≠ ev D k c := by
  intro h'
  simp only [wv, ev, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_succ_val hB] at this
  exact pos_ne_succ hB i k this

theorem cm_wv_wU (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i d ≠ wU D c := by
  intro h'
  simp only [wv, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega

theorem cm_ev_wU (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i d ≠ wU D c := by
  intro h'
  simp only [ev, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_succ_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega

theorem cm_Pt_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) {i k : Fin D.T.t} (h : i ≠ k)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i x) = Pt p D j jp i ((tieF (wv D k) (ev D k) ^ m) x) :=
  cm_Fpow_P (wv D k) (ev D k) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wv hB h c d, fun d => (cm_wv_ev hB k i d c).symm⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_ev hB i k c d, fun d => cm_ev_ev hB h c d⟩) m x

theorem cm_Pt_plus (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) (i : Fin D.T.t)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i x) =
      Pt p D j jp i ((tieF (wU D) (xiVar N r D.T.t) ^ m) x) :=
  cm_Fpow_P (wU D) (xiVar N r D.T.t) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wU hB i c d, fun d => cm_ev_wU hB i c d⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => wv_ne_xi hB i d c, fun d => ev_ne_xi hB i d c⟩) m x

theorem cm_Pt_param (hB : D.BlockOK) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (i : Fin D.T.t) (h : j i = j' i)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : Pt p D j jp i x = Pt p D j' jp' i x := by
  unfold Pt
  rw [deg_lettersAt_pos hB j jp, deg_lettersAt_pos_succ hB j jp, deg_lettersAt_pos hB j' jp', deg_lettersAt_pos_succ hB j' jp', h]

theorem cm_PL_nil (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    PL p D [] j jp x = x := rfl

theorem cm_PL_cons (i : Fin D.T.t) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : PL p D (i :: L) j jp x = Pt p D j jp i (PL p D L j jp x) := rfl

theorem cm_midGen_top (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D D.T.t j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      x := by
  unfold midGen
  rw [List.drop_eq_nil_of_le (by simp), Finset.filter_true_of_mem (fun i _ => i.2)]
  rfl

end block

theorem lattice_linear_holds : PLLin := by
  intro p _ N r _ D L j jp
  exact ⟨⟨cmPLL p D L j jp, cm_PLL_apply L j jp⟩, ⟨cmPplusL p D jp, cm_PplusL_apply jp⟩⟩

theorem comm_lattice_holds : CommPL := by
  intro p _ N r _ D hB L j jp m x
  induction L with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons i L ih =>
    refine ⟨fun k hk => ?_, ?_⟩
    · have hki : i ≠ k := fun h => hk (by simp [h])
      have hkL : k ∉ L := fun h => hk (by simp [h])
      show (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x))
      rw [cm_Pt_tie hB j jp m hki, ih.1 k hkL]
    · show (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x))
      rw [cm_Pt_plus hB j jp m i, ih.2]

theorem param_lattice_holds : ParamPL := by
  intro p _ N r _ D hB L j j' jp jp' x h
  induction L with
  | nil => rw [cm_PL_nil, cm_PL_nil]
  | cons i L ih =>
    rw [cm_PL_cons, cm_PL_cons, ih (fun a ha => h a (by simp [ha])), cm_Pt_param hB j j' jp jp' i (h i (by simp))]

theorem middle_top_holds : MidTop := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    rw [SetLike.mem_coe, cm_midGen_top, ← LinearMap.mulLeft_apply (R := ℚ_[p])]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [LinearMap.mulLeft_apply, mul_assoc _ (rename _ y) g]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    refine Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, ?_⟩
    rw [cm_midGen_top, mul_assoc _ (rename _ y) g]

theorem middle_p_eq_holds : MidPEq := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    have key : ∀ x' : MvPolynomial (BVar N r D.T.t) ℚ_[p],
        ((LinearMap.mulLeft ℚ_[p] ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp) *
          (cmPplusL p D jp * cmPLL p D (List.finRange D.T.t) j jp) :
            Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]))) x' =
        (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
          Pplus p D jp (PL p D (List.finRange D.T.t) j jp x') := by
      intro x'
      rw [Module.End.mul_apply, Module.End.mul_apply, cm_PLL_apply, cm_PplusL_apply, LinearMap.mulLeft_apply]
    rw [SetLike.mem_coe, ← key]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [key, Pall_eq]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    exact Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, by rw [Pall_eq]⟩

end Formalism.InvariantFactorPaths.KP.LL
