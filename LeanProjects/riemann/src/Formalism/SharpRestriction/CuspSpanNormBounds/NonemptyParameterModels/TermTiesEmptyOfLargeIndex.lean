import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

noncomputable section

namespace Formalism.MainNotions.S.Inh

section Comparison₂

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tie_star (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI : IsCMField D.host.E := D.host.der.cm
  have hc : D.host.conj = (IsCMField.complexConj D.host.E).restrictScalars ℚ := by
    have hg := (D.host.der.conj_iff D.host.φ₀ ((IsCMField.complexConj D.host.E).restrictScalars ℚ)).1
      (fun y => IsCMField.complexEmbedding_complexConj _ D.host.φ₀ y)
    show D.host.gal.symm _ = _
    rw [← hg, MulEquiv.symm_apply_apply]
  rw [hc]
  rfl

theorem tie_hypFE (D : D7) (i j : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
  have h1 : (VS D).hT (D.sp.hypE i) (D.sp.hypF j) = if i = j then 1 else 0 := D.sp.hyp_ef i j
  rw [← (VS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), h1]
  split_ifs <;> simp

theorem tie_hypE_indep (D : D7) : LinearIndependent D.host.E D.sp.hypE := by
  apply LinearIndependent.of_comp (LinearMap.pi (fun j => (VS D).hT (D.sp.hypF j)))
  have hfun : ⇑(LinearMap.pi (fun j => (VS D).hT (D.sp.hypF j))) ∘ D.sp.hypE =
      ⇑(Pi.basisFun D.host.E (Fin D.R.rS)) := by
    funext i j
    simp only [Function.comp_apply, LinearMap.pi_apply, Pi.basisFun_apply]
    rw [tie_hypFE]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h, Pi.single_apply]
  rw [hfun]
  exact (Pi.basisFun D.host.E (Fin D.R.rS)).linearIndependent

theorem tie_hypE_zm (D : D7) (a : Fin D.R.rS) : (VS D).hT (D.sp.hypE a) D.sp.zm = 0 := by
  have h1 : (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := (D.sp.hyp_orthz a).1
  rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a), h1, map_zero]

theorem tie_zmOf_norm (D : D7) (u : D.what₂.Word) :
    (VS D).hT (D.zmOf u) (D.zmOf u) = -((Tu D u : ℕ) : D.host.E) := by
  have hc : D.cOf u ≠ 0 := D.cOf_ne u
  have hcc : D.host.conj (D.cOf u) ≠ 0 := by
    intro h; apply hc; rw [← tie_star] at h; exact star_eq_zero.1 h
  have hq := D.cOf_eq u
  have hsp : D.sp.T = (D.mem D.u₀).A.T := D.sp_T
  have hz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    have h0 : (VS D).hT D.sp.zm D.sp.zm = -(D.sp.T : D.host.E) := D.sp.zm_norm
    rw [h0, hsp]
  show (VS D).hT ((D.cOf u)⁻¹ • D.sp.zm) ((D.cOf u)⁻¹ • D.sp.zm) = _
  rw [LinearMap.map_smulₛₗ₂, map_smul, hz, ← hq]
  simp only [Tu, smul_eq_mul, starRingEnd_apply, star_inv₀, tie_star]
  field_simp
  <;> ring

def tie_flag0 (D : D7) (u : D.what₂.Word) : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) where
  e := D.sp.hypE
  z := D.zmOf u
  e_indep := tie_hypE_indep D
  e_iso := D.sp.hyp_ee
  z_orth := fun a => by
    unfold D7.zmOf
    rw [map_smul, tie_hypE_zm, smul_zero]
  z_norm := tie_zmOf_norm D u

theorem tie_flagG_nonempty (D : D7) (u : D.what₂.Word) :
    ∃ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE ∧ F0.z = D.zmOf u := ⟨tie_flag0 D u, rfl, rfl⟩

theorem tie_lflag_nonempty (D : D7) (u : D.what₂.Word) :
    Nonempty (LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) := ⟨⟨tie_flag0 D u, 0⟩⟩

theorem tie_termTie_of_noTerms (D : D7) (h : ∀ u u', IsEmpty (D.s.Term u u')) : Nonempty (TermTie D) := by
  have hex : ∀ u, ∃ n : ℕ, (n : ℝ) = dimPi (hc := D.hcW) u := fun u =>
    ⟨_, by first | exact Nat.cast_prod _ _ | (unfold dimPi; exact Nat.cast_prod _ _)⟩
  choose nd hnd using hex
  exact ⟨{
    abelian₂ := fun t => ((h _ _).false t).elim
    fl := fun t => ((h _ _).false t).elim
    fl' := fun t => ((h _ _).false t).elim
    fixed := fun t => ((h _ _).false t).elim
    lift' := fun t => ((h _ _).false t).elim
    adm := fun t => ((h _ _).false t).elim
    conv' := fun t => ((h _ _).false t).elim
    inS_iff := fun t => ((h _ _).false t).elim
    isId_iff := fun t => ((h _ _).false t).elim
    G_eq := fun t => ((h _ _).false t).elim
    rel_iff := fun t => ((h _ _).false t).elim
    FeqF_iff := fun t => ((h _ _).false t).elim
    id_G := fun t => ((h _ _).false t).elim
    gen_iff := fun t => ((h _ _).false t).elim
    pt_cell := fun t => ((h _ _).false t).elim
    pLam := fun p => ((h _ _).false (D.s.pfst p)).elim
    pfl := fun p => ((h _ _).false (D.s.pfst p)).elim
    beta := fun p => ((h _ _).false (D.s.pfst p)).elim
    isPair := fun p => ((h _ _).false (D.s.pfst p)).elim
    s0_eq := fun p => ((h _ _).false (D.s.pfst p)).elim
    scal_iff := fun p => ((h _ _).false (D.s.pfst p)).elim
    wRow := fun p => ((h _ _).false (D.s.pfst p)).elim
    wRow_pos := fun p => ((h _ _).false (D.s.pfst p)).elim
    chi := fun p => ((h _ _).false (D.s.pfst p)).elim
    chi_norm := fun p => ((h _ _).false (D.s.pfst p)).elim
    Hpi := fun u => EuclideanSpace ℂ (Fin (nd u))
    Hpi_dim := fun u => by rw [finrank_euclideanSpace_fin]; exact hnd u
    Jt := fun t => ((h _ _).false t).elim
    piB := fun p => ((h _ _).false (D.s.pfst p)).elim
    piB_unit := fun p => ((h _ _).false (D.s.pfst p)).elim
    pval_eq := fun p => ((h _ _).false (D.s.pfst p)).elim }⟩

theorem tie_termTie_example (H : Host Formalism.BasicNotions.Examples₂.R0) (T : ℕ) [Fact T.Prime]
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : Formalism.BasicNotions.Examples₂.THyp H)
    (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
    (G : Formalism.BasicNotions.Examples₂.LocalGap H) :
    Nonempty (TermTie (Formalism.BasicNotions.Examples₂.exampleRecordOfData H T hg ht hlev hpde pz hK hpz hcong G)) :=
  tie_termTie_of_noTerms _ (fun _ _ => ⟨fun t => Empty.elim t⟩)

theorem tie_termTie_isEmpty_of_id (D : D7) {u u' : D.what₂.Word} (t : D.s.Term u u') (h1 : D.s.isId t)
    (h2 : D.s.Gterm t ≠ 0) : IsEmpty (TermTie D) := ⟨fun X => h2 (X.id_G t h1)⟩

theorem tie_termTie_isEmpty_of_FeqF (D : D7) {u u' : D.what₂.Word} (t : D.s.Term u u') (h1 : D.s.FeqF t)
    (h2 : ¬ D.s.isId t) : IsEmpty (TermTie D) := by
  refine ⟨fun X => h2 ((X.isId_iff t).2 ?_)⟩
  obtain ⟨n, hn, hfr⟩ := (X.FeqF_iff t).1 h1
  refine ⟨n, hn, fun a => ?_, ?_⟩
  · have ha := hfr a.castSucc
    simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at ha
    exact ha
  · have hz := hfr (Fin.last _)
    simp only [frame, FlagG.fvec, Fin.snoc_last] at hz
    rw [hz, sub_self]
    exact zero_mem _

theorem term_ties_empty_of_large_index (D : D7) {u u' : D.what₂.Word} (p : D.s.Pair u u') (h : D.R.k < D.s.s0 p) :
    IsEmpty (TermTie D) := by
  refine ⟨fun X => ?_⟩
  rw [X.s0_eq p] at h
  unfold Lat.s0 at h
  omega

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem tie_frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem admissible_flag_refl (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) : IsAdmissible Λ g F F := by
  unfold IsAdmissible AdmWit
  refine ⟨1, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, fun b => ?_⟩
  rw [tie_frameAct_one, sub_self]
  unfold ModG
  intro P _
  exact zero_mem _

theorem tie_autLam_refl (Λ : Submodule (𝓞 E) S.V) : IsAutLam S Λ (LinearEquiv.refl E S.V) := by
  unfold IsAutLam
  refine ⟨?_, ?_⟩
  · first
      | exact (Formalism.HermitianLatticesTheory.isom S.hT).one_mem
      | exact fun x y => rfl
  · ext x
    simp [Formalism.HermitianLatticesTheory.gmap]

theorem tie_pair_self (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    IsPair Λ F F' F' (LinearEquiv.refl E S.V) g := by
  unfold IsPair IotaCompat
  refine ⟨tie_autLam_refl Λ, fun j => ?_, rfl, fun x' _ l _ => Iff.rfl⟩
  simp

theorem tie_refl_mem_NLam (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) :
    LinearEquiv.refl E S.V ∈ NLam Λ F := by
  simp only [NLam, Set.mem_setOf_eq]
  refine ⟨tie_autLam_refl Λ, fun j x _ => ?_, fun x _ => ?_⟩ <;> simp

end Gen

theorem tie_idTerm_ok (D : D7) (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T : D.host.E}
    (F : LFlag (hS D) D.R.rS T) (h : FixedHyp D Λ F) :
    IsLift Λ F ∧ IsAdmissible Λ (gS D) F F ∧ IsFixedConv Λ (gS D) F ∧
      IsPair Λ F F F (LinearEquiv.refl _ _) (gS D) := by
  unfold FixedHyp at h
  obtain ⟨-, -, h3, h4⟩ := h
  exact ⟨h3, admissible_flag_refl Λ (gS D) F, h4, tie_pair_self Λ (gS D) F F⟩

section Gen2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem tie_e_X {T : E} (F : FlagG S r T) (a : Fin r) {x : S.V} (hx : x ∈ F.X) : S.hT (F.e a) x = 0 := by
  have hle : Submodule.span E (Set.range F.e) ≤ LinearMap.ker (S.hT (F.e a)) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (F.e_iso a b))
  exact LinearMap.mem_ker.mp (hle hx)

theorem tie_mem_orth {T : E} (F : FlagG S r T) {y : S.V} (hy : ∀ a, S.hT (F.e a) y = 0) : y ∈ orth S F.X := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact hy a
  | zero => simp
  | add u w _ _ hu hw => simp [hu, hw]
  | smul c u _ hu => simp [hu]

theorem tie_idCell_row (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')
    (h : ∃ n ∈ NLam Λ F, (∀ a, n (F.fl.e a) = F'.fl.e a) ∧ n F.fl.z - F'.fl.z ∈ Xsp F)
    (a : Fin r) (b : Fin (r + 1)) : ZhatL F F' a.castSucc b = 0 := by
  obtain ⟨n, hn, he, hz⟩ := h
  simp only [NLam, Set.mem_setOf_eq] at hn
  obtain ⟨-, hflag, horth⟩ := hn
  have hX : ∀ v ∈ F.fl.X, S.hT (F.fl.e a) v = 0 := fun v hv => tie_e_X F.fl a hv
  have hXa : ∀ j, Xflag F j ≤ F.fl.X := fun j => by
    show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (Set.range F.fl.e)
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hfa : F.fl.fvec a.castSucc = F.fl.e a := by simp only [FlagG.fvec, Fin.snoc_castSucc]
  show S.hT (F.fl.fvec a.castSucc) (F'.fl.fvec b) = 0
  rw [hfa]
  cases b using Fin.lastCases with
  | last =>
    have hfz : F'.fl.fvec (Fin.last r) = F'.fl.z := by simp only [FlagG.fvec, Fin.snoc_last]
    rw [hfz]
    have hzo : F.fl.z ∈ orth S (Xsp F) := tie_mem_orth F.fl F.fl.z_orth
    have h1 := horth _ hzo
    have e1 := hX _ h1
    have e2 := hX _ hz
    have e3 := F.fl.z_orth a
    have hsplit : S.hT (F.fl.e a) F'.fl.z = S.hT (F.fl.e a) F.fl.z +
        S.hT (F.fl.e a) (n F.fl.z - F.fl.z) - S.hT (F.fl.e a) (n F.fl.z - F'.fl.z) := by
      rw [← map_add, ← map_sub]
      congr 1
      abel
    rw [hsplit, e1, e2, e3]
    simp
  | cast c =>
    have hfc : F'.fl.fvec c.castSucc = F'.fl.e c := by simp only [FlagG.fvec, Fin.snoc_castSucc]
    rw [hfc, ← he c]
    have hc : F.fl.e c ∈ Submodule.span E (F.fl.e '' {i | i.1 < c.val + 1}) :=
      Submodule.subset_span ⟨c, by simp, rfl⟩
    have h1 := hflag c.val _ hc
    have e1 := hX _ (hXa _ h1)
    have hsplit : S.hT (F.fl.e a) (n (F.fl.e c)) = S.hT (F.fl.e a) (F.fl.e c) +
        S.hT (F.fl.e a) (n (F.fl.e c) - F.fl.e c) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, e1, F.fl.e_iso a c, add_zero]

theorem tie_idCell_G (hr : 0 < r) (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')
    (h : ∃ n ∈ NLam Λ F, (∀ a, n (F.fl.e a) = F'.fl.e a) ∧ n F.fl.z - F'.fl.z ∈ Xsp F) :
    Gval F F' = 0 := by
  have hrow : ∀ (a : Fin r) b, ZhatL F F' a.castSucc b = 0 := fun a b => tie_idCell_row Λ F F' h a b
  have hD : ∀ l, 1 ≤ l → Dl F.fl F'.fl l = 0 := by
    intro l hl
    unfold Dl leadMinorE
    split_ifs with hle
    · apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, by omega⟩
      intro j
      exact hrow ⟨0, hr⟩ (Fin.castLE hle j)
    · rfl
  show Gflag F.fl F'.fl = 0
  unfold Gflag
  rw [hD (r + 1) (by omega), hD r hr]
  simp

end Gen2

theorem tie_one_lt_b (D : D7) (large₂ : SizeData₂ D) : 1 < large₂.sc.b := by
  have hx := large₂.sc.one_lt_alt
  have hpos : 0 < large₂.sc.x ^ large₂.sc.eps := Real.rpow_pos_of_pos (by linarith) _
  show 1 < Real.exp (large₂.sc.x ^ large₂.sc.eps)
  linarith [Real.add_one_lt_exp (ne_of_gt hpos)]

theorem tie_normWin_one (D : D7) (large₂ : SizeData₂ D) {C1 : ℝ} (h : 0 ≤ C1) : normWin D large₂ C1 1 := by
  unfold normWin
  have hb := (tie_one_lt_b D large₂).le
  have hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg h (sq_nonneg _)
  exact ⟨Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith), Real.one_le_rpow hb hc⟩

theorem tie_loopTie_isEmpty_of_neg (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) {C1 : ℝ}
    (h : C1 < 0) (hm : 0 < D.R.m) : IsEmpty (LoopTie D large₂ X u u' C1) := by
  refine ⟨fun Y => ?_⟩
  have hw := Y.θ_win
  unfold normWin at hw
  have hb := tie_one_lt_b D large₂
  have hm' : (0 : ℝ) < (D.R.m : ℝ) := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (D.R.m : ℝ) ^ 2 := pow_pos hm' 2
  have hneg : C1 * (D.R.m : ℝ) ^ 2 < -(C1 * (D.R.m : ℝ) ^ 2) := by
    linarith [mul_neg_of_neg_of_pos h hm2]
  have hlt := Real.rpow_lt_rpow_of_exponent_lt hb hneg
  linarith [hw.1, hw.2]

def tie_HRows (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (tie_flag0 D u) what₂

def tie_HRowsPos (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (tie_flag0 D u) what₂ ∧
    0 < ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D (tie_flag0 D u) Λ

def tie_HAmp (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C1 : ℝ) : Prop :=
  ∃ θ : ℝ, normWin D large₂ C1 θ ∧ ∃ W : D.what₂.Tau → LocW D.R.k D.R.rS, (∀ τ, GoodW D τ u u' θ (W τ)) ∧
    ∃ A : ∀ τ, LocS (W τ), (∀ τ, GoodS D (lamD D τ) (A τ)) ∧ ∀ τ, (A τ).deg = D.dsig τ

theorem tie_loopTie_of_noTerms (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (h : IsEmpty (D.s.Term u u')) (hR : tie_HRows D u) (hA : tie_HAmp D large₂ u u' C1) :
    Nonempty (LoopTie D large₂ X u u' C1) := by
  unfold tie_HRows at hR
  unfold tie_HAmp at hA
  obtain ⟨what₂, hrows⟩ := hR
  obtain ⟨θ, hθ, W, hW, A, hAS, hdeg⟩ := hA
  exact ⟨{
    F0 := tie_flag0 D u
    flag_e_eq_hyperbolic := rfl
    formsAtZero := rfl
    what₂ := what₂
    isRows := hrows
    fl_eq := fun t => (h.false t).elim
    Lam_mem := fun t => (h.false t).elim
    frame_ok := fun t => (h.false t).elim
    wRow_eq := fun p => (h.false (D.s.pfst p)).elim
    pair_inj := fun p => (h.false (D.s.pfst p)).elim
    θ := θ
    θ_win := hθ
    W := W
    goodW := hW
    A := A
    goodS := hAS
    deg_eq := hdeg
    γ := fun t => (h.false t).elim
    pt := fun t => (h.false t).elim
    θR := fun t => (h.false t).elim
    νR := fun t => (h.false t).elim
    volR := fun t => (h.false t).elim
    volR_pos := fun t => (h.false t).elim
    gram := fun t => (h.false t).elim
    rel := fun t => (h.false t).elim
    J_irr := fun t => (h.false t).elim
    J_norm := fun t => (h.false t).elim }⟩

theorem tie_HAmp_of_loopTie (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) : tie_HAmp D large₂ u u' C1 := by
  unfold tie_HAmp
  exact ⟨Y.θ, Y.θ_win, Y.W, Y.goodW, Y.A, Y.goodS, Y.deg_eq⟩

theorem tie_loopTie_aut_finite (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (p : D.s.Pair u u') :
    0 < Nat.card (autLz D Y.F0 (X.abelian₂ (D.s.pfst p))) := by
  have h1 := X.wRow_pos p
  rw [Y.wRow_eq p] at h1
  unfold Formalism.MainNotions.S.wRow at h1
  refine Nat.pos_of_ne_zero (fun h0 => ?_)
  rw [h0] at h1
  simp at h1

theorem loop_ties_of_no_terms (D : D7) (large₂ : SizeData₂ D) (Cn : ℝ) (h : ∀ u u', IsEmpty (D.s.Term u u'))
    (hR : ∀ u, tie_HRows D u) (hA : ∀ u u', tie_HAmp D large₂ u u' Cn) : Nonempty (Formalism.MainNotions.UniformConstantsAndStatements.Ties D large₂ Cn) := by
  obtain ⟨X⟩ := tie_termTie_of_noTerms D h
  exact ⟨⟨X, fun u u' => (tie_loopTie_of_noTerms D large₂ X u u' Cn (h u u') (hR u) (hA u u')).some⟩⟩

theorem loop_ties_nonempty_iff (D : D7) (large₂ : SizeData₂ D) (Cn : ℝ) :
    Nonempty (Formalism.MainNotions.UniformConstantsAndStatements.Ties D large₂ Cn) ↔ ∃ X : TermTie D, ∀ u u', Nonempty (LoopTie D large₂ X u u' Cn) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.X, fun u u' => ⟨T.Y u u'⟩⟩
  · rintro ⟨X, hY⟩
    exact ⟨⟨X, fun u u' => (hY u u').some⟩⟩

section BC

open Formalism.MainNotions.S.LocalSplitGroups

theorem tie_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hcol : ∀ i, S.hT (S.frame i) (∑ j, v j • S.frame j) = 0 := by
    intro i
    have hi := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← hi]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hall : ∀ x, S.hT x (∑ j, v j • S.frame j) = 0 := by
    intro x
    have hx : x ∈ Submodule.span E (Set.range S.frame) := by
      rw [S.frame.span_eq]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact hcol i
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add u w _ _ hu hw => rw [map_add, LinearMap.add_apply, hu, hw, add_zero]
    | smul c u _ hu => rw [map_smulₛₗ, LinearMap.smul_apply, hu, smul_zero]
  have hy0 : ∑ j, v j • S.frame j = 0 := S.nondeg.2 _ hall
  exact hv0 (funext (Fintype.linearIndependent_iff.mp S.frame.linearIndependent v hy0))

variable (D : D7) (p : PlF D)

def tie_Gp : Matrix (Fin (hS D).rank) (Fin (hS D).rank) (D.s.atP p).Ep := (hS D).gram.map (D.s.atP p).ιE

theorem tie_Gp_unit : IsUnit (tie_Gp D p).det := by
  unfold tie_Gp
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (isUnit_iff_ne_zero.mpr (tie_gram_det_ne (hS D))).map _

theorem tie_cj_iota (x : D.host.E) : (D.s.atP p).cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) := by
  rw [(D.s.atP p).cj_ιE, D.conjF_eq, tie_star]

theorem tie_Gp_cj (i j : Fin (hS D).rank) : (D.s.atP p).cj (tie_Gp D p j i) = tie_Gp D p i j := by
  simp only [tie_Gp, Matrix.map_apply]
  rw [tie_cj_iota]
  congr 1
  simp only [HSpace.gram]
  exact (hS D).herm.eq _ _

def tie_hp (x y : Fin (hS D).rank → (D.s.atP p).Ep) : (D.s.atP p).Ep :=
  ∑ j, ∑ i, (D.s.atP p).cj (y j) * (tie_Gp D p j i * x i)

def tie_Hp (M : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hcj : M.L.cj = (D.s.atP p).cj) :
    Loc.HermSp M (Fin (hS D).rank → (D.s.atP p).Ep) where
  h := tie_hp D p
  h_add_left := fun x x' y => by
    simp only [tie_hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  h_smul_left := fun a x y => by
    simp only [tie_hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  h_herm := fun x y => by
    have hcc : ∀ z, (D.s.atP p).cj ((D.s.atP p).cj z) = z := fun z => by
      have := M.L.cj_cj z; rwa [hcj] at this
    rw [hcj]
    simp only [tie_hp, map_sum, map_mul, hcc, tie_Gp_cj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  nondeg := fun x hx => by
    classical
    have h1 : (tie_Gp D p).mulVec x = 0 := by
      funext j
      have := hx (Pi.single j 1)
      simp only [tie_hp] at this
      rw [Finset.sum_eq_single j] at this
      · simpa [Matrix.mulVec, dotProduct] using this
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    have h2 : (tie_Gp D p)⁻¹ * tie_Gp D p = 1 := Matrix.nonsing_inv_mul _ (tie_Gp_unit D p)
    calc x = ((tie_Gp D p)⁻¹ * tie_Gp D p).mulVec x := by rw [h2, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  free := inferInstance
  fin := inferInstance

def tie_bc : (hS D).V →+ (Fin (hS D).rank → (D.s.atP p).Ep) where
  toFun x := fun i => (D.s.atP p).ιE ((hS D).frame.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem tie_bc_form (x y : (hS D).V) :
    tie_hp D p (tie_bc D p x) (tie_bc D p y) = (D.s.atP p).ιE (brS (hS D) x y) := by
  have hbc : ∀ v, tie_bc D p v = fun i => (D.s.atP p).ιE ((hS D).frame.repr v i) := fun v => rfl
  have key : (hS D).hT y x = ∑ j, ∑ i, star ((hS D).frame.repr y j) *
      ((hS D).gram j i * (hS D).frame.repr x i) := by
    conv_lhs => rw [← (hS D).frame.sum_repr y, ← (hS D).frame.sum_repr x]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, HSpace.gram, Finset.mul_sum, RingHom.id_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hbc, hbc, show brS (hS D) x y = (hS D).hT y x from rfl, key]
  simp only [tie_hp, tie_Gp, Matrix.map_apply, tie_cj_iota, map_sum, map_mul]

theorem tie_Ep_nontrivial : Nontrivial (D.s.atP p).Ep := by
  have hr := (D.s.atP p).rank
  exact Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [hr]; norm_num)

theorem tie_termLoc_of_noTerms (Y : TermTie D) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hcj : ∀ p, (M p).L.cj = (D.s.atP p).cj)
    (u u' : D.what₂.Word) (h : IsEmpty (D.s.Term u u')) (hR : tie_HRowsPos D u) : Nonempty (TermLoc D Y δ M u u') := by
  classical
  obtain ⟨what₂, hrows, hpos⟩ := hR
  have hP : IsEmpty (D.s.Pair u u') := ⟨fun q => h.elim (D.s.pfst q)⟩
  exact ⟨{
    V := fun p => Fin (hS D).rank → (D.s.atP p).Ep
    acg := fun _ => inferInstance
    mod := fun _ => inferInstance
    H := fun p => tie_Hp D p (M p) (hcj p)
    rank := fun p => by
      have := tie_Ep_nontrivial D p
      rw [Module.finrank_fin_fun]
      have := D.sp.Y_rank 0 (Nat.zero_le _)
      simpa [Ranks.rankY] using this
    bc := fun p => tie_bc D p
    bc_smul := fun p a x => by
      funext i
      show (D.s.atP p).ιE ((hS D).frame.repr (a • x) i) =
        (D.s.atP p).ιE a * (D.s.atP p).ιE ((hS D).frame.repr x i)
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    bc_span := fun p => by
      rw [eq_top_iff, ← (Pi.basisFun (D.s.atP p).Ep (Fin (hS D).rank)).span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨(hS D).frame i, ?_⟩
      funext j
      simp [tie_bc, Finsupp.single_apply, Pi.single_apply, eq_comm]
    bc_form := fun p x y => tie_bc_form D p x y
    sgn := fun _ _ => 1
    sgn' := fun _ _ => 1
    sgn_sq := fun _ _ => by simp
    loc := fun t => isEmptyElim t
    loc_Lam := fun t => isEmptyElim t
    loc_f := fun t => isEmptyElim t
    loc_f' := fun t => isEmptyElim t
    local_group_in_family_nontrivial := fun t => isEmptyElim t
    G_pt := fun t => isEmptyElim t
    generic_iff := fun t => isEmptyElim t
    at_pt := fun t => isEmptyElim t
    scalar_loc := fun q => isEmptyElim q
    massT := fun t => isEmptyElim t
    massT_nonneg := fun t => isEmptyElim t
    massTot := ∑ Λ ∈ what₂, Formalism.MainNotions.S.wRow D (tie_flag0 D u) Λ
    massTot_pos := hpos
    mass_def := ⟨tie_flag0 D u, what₂, rfl, rfl, hrows, rfl, fun t => isEmptyElim t⟩
    term_inj := fun t => isEmptyElim t
    massPair_eq := fun q => isEmptyElim q }⟩

theorem tie_termLocs_of_noTerms (Y : TermTie D) (h : ∀ u u', IsEmpty (D.s.Term u u')) (hR : ∀ u, tie_HRowsPos D u) :
    Nonempty (TermLocs D Y) := by
  refine ⟨fun δ M hA u u' => (tie_termLoc_of_noTerms D Y δ M (fun p => ?_) u u' (h u u') (hR u)).some⟩
  have hp := hA p
  unfold Agree at hp
  exact hp.2.2.1

end BC

section Pt0

open Formalism.MainNotions.S.LocalSplitGroups

theorem tie_ptEntry_diag {K : Type*} [Zero K] (ds : List K) (i j : ℕ) :
    ptEntry (ds.map (fun t => (t, 1))) i j = if i = j then ds.getD i 0 else 0 := by
  induction ds generalizing i j with
  | nil => simp [ptEntry]
  | cons d ds ih =>
    rcases i with _ | i <;> rcases j with _ | j <;> simp [ptEntry, ih]

def tie_diagPt {K : Type*} [Zero K] {n : ℕ} (f : Fin n → K) (hf : ∀ a, f a ≠ 0) : Point K n :=
  ⟨(List.ofFn f).map (fun t => (t, 1)), by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' f t).1 ht
    exact ⟨hf a, le_refl 1⟩, by
    have h : ((List.ofFn f).map (fun t => (t, 1))).map Prod.snd = List.replicate n 1 := by
      rw [List.map_map]
      apply List.ext_getElem <;> simp
    rw [h]; simp⟩

theorem tie_diagPt_mat {K : Type*} [Zero K] {n : ℕ} (f : Fin n → K) (hf : ∀ a, f a ≠ 0) :
    ptMat (tie_diagPt f hf) = Matrix.diagonal f := by
  ext a b
  simp only [ptMat, tie_diagPt]
  rw [tie_ptEntry_diag]
  by_cases h : a = b
  · subst h
    simp [List.getD_eq_getElem, Matrix.diagonal_apply_eq]
  · simp [h, Fin.val_inj, Matrix.diagonal_apply_ne _ h]

theorem zero_of_gram_point_exists (D : D7) (u u' : D.what₂.Word) :
    ∃ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w = 0 := by
  classical
  have hT0 : (((D.mem D.u₀).A.T : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast (D.mem D.u₀).A.T_prime.ne_zero
  have hc := D.cOf_ne u
  have hc' := D.cOf_ne u'
  have hcc : D.host.conj (D.cOf u) ≠ 0 := fun h => hc ((map_eq_zero_iff _ D.host.conj.injective).1 h)
  have hcc' : D.host.conj (D.cOf u') ≠ 0 := fun h => hc' ((map_eq_zero_iff _ D.host.conj.injective).1 h)
  let x : D.host.E := (((D.mem D.u₀).A.T : ℕ) : D.host.E) / (D.cOf u * D.cOf u')
  have hx0 : x ≠ 0 := div_ne_zero hT0 (mul_ne_zero hc hc')
  let f : Fin (D.R.rS + 1) → D.host.E := fun a => if (a : ℕ) = D.R.rS then x else 1
  have hf : ∀ a, f a ≠ 0 := fun a => by
    simp only [f]
    split_ifs
    · exact hx0
    · exact one_ne_zero
  have hA : ((Matrix.diagonal f).submatrix (Fin.castLE (le_refl (D.R.rS + 1)))
      (Fin.castLE (le_refl (D.R.rS + 1)))).det = x := by
    rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Fin.prod_univ_castSucc]
    have h1 : ∀ i : Fin D.R.rS, (f ∘ Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castSucc i) = 1 := fun i => by
      simp [f, i.isLt.ne]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const_one, one_mul]
    simp [f]
  have hB : ((Matrix.diagonal f).submatrix (Fin.castLE (Nat.le_succ D.R.rS))
      (Fin.castLE (Nat.le_succ D.R.rS))).det = 1 := by
    rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    exact Finset.prod_eq_one (fun i _ => by simp [f, i.isLt.ne])
  have hxx : x * D.host.conj x = (((D.mem u).A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E) := by
    have e1 := D.cOf_eq u
    have e2 := D.cOf_eq u'
    simp only [x, map_div₀, map_mul, map_natCast]
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero (mul_ne_zero hc hc') (mul_ne_zero hcc hcc'))]
    nth_rewrite 1 [← e1]
    rw [← e2]
    ring
  refine ⟨tie_diagPt f hf, ?_⟩
  unfold Gpt Dmin
  rw [dif_pos le_rfl, dif_pos (Nat.le_succ _), tie_diagPt_mat, hA, hB, D.conjF_eq, D.conjF_eq, map_one, hxx]
  ring

end Pt0

theorem tie_cells_top_of_tie (D : D7) (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) (hr : D.s.relevant t) :
    ∃ p : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (X.fl t) (X.fl' t))) p := ⟨D.s.ptOf t, X.pt_cell t hG hr⟩

theorem tie_pval_irr_of_tie (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (p : D.s.Pair u u') (hG : D.s.Gterm (D.s.pfst p) ≠ 0)
    (hr : ¬ D.s.relevant (D.s.pfst p)) : D.s.pval p = 0 := by
  rw [X.pval_eq p, Y.J_irr _ hG hr, ContinuousLinearMap.zero_comp]
  unfold hsInner
  simp

theorem tie_all_of_noTerms (D : D7) (large₂ : SizeData₂ D) (Cw : ℝ) (h : ∀ u u', IsEmpty (D.s.Term u u'))
    (hR : ∀ u, tie_HRows D u) (hRp : ∀ u, tie_HRowsPos D u) (hA : ∀ u u', tie_HAmp D large₂ u u' Cw) :
    ∃ X : TermTie D, (∀ u u', Nonempty (LoopTie D large₂ X u u' Cw)) ∧ Nonempty (Formalism.MainNotions.S.LocalSplitGroups.TermLocs D X) := by
  obtain ⟨X⟩ := tie_termTie_of_noTerms D h
  exact ⟨X, fun u u' => tie_loopTie_of_noTerms D large₂ X u u' Cw (h u u') (hR u) (hA u u'),
    tie_termLocs_of_noTerms D X h hRp⟩

def tie_HRowLat (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ Λ : Submodule (𝓞 D.host.E) (VS D).V, IsRowLat D (tie_flag0 D u) Λ

theorem tie_rows_empty_of_not_HRowLat (D : D7) (u : D.what₂.Word) (h : ¬ tie_HRowLat D u) :
    IsRowReps D (tie_flag0 D u) ∅ := by
  unfold tie_HRowLat at h
  unfold IsRowReps
  exact ⟨fun Λ hΛ => by simp at hΛ, fun Λ hΛ => (h ⟨Λ, hΛ⟩).elim⟩

theorem tie_HRowLat_of_term (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (t : D.s.Term u u') : ∃ Λ, IsRowLat D Y.F0 Λ := by
  have hr := Y.isRows
  unfold IsRowReps at hr
  exact ⟨X.abelian₂ t, hr.1 _ (Y.Lam_mem t)⟩

end Comparison₂

end Formalism.MainNotions.S.Inh
