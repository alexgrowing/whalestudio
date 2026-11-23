import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace KC

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by
    ext g; rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem mul_val_mem {x : Mat n} (hx : x ∈ GLs n) (y : G n) : x * y.val ∈ GLs n := by
  show (x * y.val).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

section Congr

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (X : Mat n) : EqOn (Rd X f₁) (Rd X f₂) (GLs n) := by
  intro g hg
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (h.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg))]

theorem eu_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f₁) (Eu s a b f₂) (GLs n) := by
  intro g hg
  have h1 := rd_congr h (Matrix.single a b 1) hg
  have h2 := rd_congr h (Matrix.single a b Complex.I) hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2]

theorem epow_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), EqOn (Epow s m a b f₁) (Epow s m a b f₂) (GLs n)
  | 0, a, b => by
    intro g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | m + 1, a, b => by
    intro g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (epow_congr h s m c b) s a c hg

theorem gel_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f₁) (gel s m f₂) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem zop_congr : ∀ (w : List (Bool × ℕ)) {f₁ f₂ : Mat n → V}, EqOn f₁ f₂ (GLs n) →
    EqOn (zOp w f₁) (zOp w f₂) (GLs n)
  | [], _, _, h => h
  | p :: w, _, _, h => by
    intro g hg
    exact gel_congr (zop_congr w h) p.1 p.2 hg

end Congr

section Props

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem gel_ninv (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {F : Mat n → V}
    (hF : ContDiffOn ℝ ∞ F (GLs n)) (hN : NInv W₁ W₂ F) (s : Bool) (m : ℕ) : NInv W₁ W₂ (gel s m F) := by
  intro u hu x hx
  have h1 := ((hGC n V V s m F hF).2 x hx).2.1 u.val (val_mem u)
  rw [← h1.1]
  exact gel_congr (fun y hy => hN u hu y hy) s m hx

theorem zop_props (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      ContDiffOn ℝ ∞ (zOp w F) (GLs n) ∧ NInv W₁ W₂ (zOp w F)
  | [], F, hF, hN => ⟨hF, hN⟩
  | p :: w, F, hF, hN => by
    obtain ⟨h1, h2⟩ := zop_props hGC w F hF hN
    exact ⟨(hGC n V V p.1 p.2 _ h1).1, gel_ninv hGC h1 h2 p.1 p.2⟩

theorem zop_field (hGC : GelComm) (hGF : GelFlag) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (A : Mat n → (V →L[ℂ] V)) (hA : ContDiffOn ℝ ∞ A (GLs n)) (hQ : QInv W₁ W₂ A) :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      EqOn (zOp w (fun y => A y (F y))) (fun y => A y (zOp w F y)) (GLs n)
  | [], _, _, _ => fun _ _ => rfl
  | p :: w, F, hF, hN => by
    intro x hx
    have ih := zop_field hGC hGF hW A hA hQ w F hF hN
    obtain ⟨h1, h2⟩ := zop_props hGC w F hF hN
    show gel p.1 p.2 (zOp w (fun y => A y (F y))) x = A x (gel p.1 p.2 (zOp w F) x)
    rw [gel_congr ih p.1 p.2 hx]
    exact hGF n V W₁ W₂ hW A (zOp w F) hA h1 hQ h2 p.1 p.2 x hx

end Props

section Slice

variable {P Q W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slice_eq {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (p : P) :
    ∀ m : ℕ, ∀ x ∈ O, iteratedFDeriv ℝ m (fun y => U (p, y)) x =
      (iteratedFDeriv ℝ m U (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)
  | 0, x, _ => by
    ext h
    simp [iteratedFDeriv_zero_apply]
  | m + 1, x, hx => by
    have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
    have hpx : (p, x) ∈ (Set.univ ×ˢ O : Set (P × Q)) := ⟨trivial, hx⟩
    have hev : (iteratedFDeriv ℝ m (fun y => U (p, y))) =ᶠ[nhds x]
        (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) :=
      Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => slice_eq hO hU p m y hy
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m U) (p, x) := by
      have h1 := hU.differentiableOn_iteratedFDerivWithin (m := m) (by exact_mod_cast ENat.natCast_lt_top m) hS.uniqueDiffOn
      have h2 : DifferentiableOn ℝ (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
        h1.congr fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
      exact h2.differentiableAt (hS.mem_nhds hpx)
    have hj : HasFDerivAt (fun y : Q => (p, y)) (ContinuousLinearMap.inr ℝ P Q) x := hasFDerivAt_prodMk_right p x
    have hC : HasFDerivAt (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q))
        (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) (iteratedFDeriv ℝ m U (p, x)) :=
      ContinuousLinearMap.hasFDerivAt _
    have hcomp := hC.comp x (hdiff.hasFDerivAt.comp x hj)
    have hfun : (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) =
        ⇑(ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) ∘ iteratedFDeriv ℝ m U ∘ Prod.mk p := by
      funext y; rfl
    ext h
    rw [iteratedFDeriv_succ_apply_left, hev.fderiv_eq, hfun, hcomp.fderiv]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    rw [iteratedFDeriv_succ_apply_left]
    rfl

theorem slice_cont {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (m : ℕ) :
    ContinuousOn (fun q : P × Q => iteratedFDeriv ℝ m (fun y => U (q.1, y)) q.2) (Set.univ ×ˢ O) := by
  have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
  have h1 : ContinuousOn (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
    (hU.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top) hS.uniqueDiffOn).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
  have h2 := ((ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)).continuous.comp_continuousOn h1)
  refine h2.congr fun q hq => ?_
  have := slice_eq hO hU q.1 m q.2 hq.2
  simp only [Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  rw [this]

end Slice

end KC

open KC in
theorem kerComm_of (hWN : WaveN) (hWA : WaveA) : KerComm := by
  intro hWE hWS hGC hGF hIS n _ _ μ _ E w g T k hg hk W₁ W₂ hW A hA hQ f hf hfN x hx
  obtain ⟨u, hu, hu0, huN⟩ := hWN hWE hWS hGC n E W₁ W₂ f hf hfN
  have hv := hWA hGF n E W₁ W₂ hW A u hA hQ hu huN
  have h1 := hk.2.2.2 _ hv x hx
  have h2 := hk.2.2.2 _ hu x hx

  have hS : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) := isOpen_univ.prod isOpen_GLs
  have hgc : ContDiff ℝ ∞ fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
  have hU' : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) • u p.1 p.2) (Set.univ ×ˢ GLs n) :=
    hgc.contDiffOn.smul hu.1
  have hFs : ContDiffOn ℝ ∞ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') (GLs n) := by
    refine hIS n ℝ MeasureTheory.volume E.V (fun t x' => ((g t : ℝ) : ℂ) • u t x') ?_ ?_ ?_
    · intro t
      exact hU'.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) fun y hy => ⟨trivial, hy⟩
    · intro m
      exact slice_cont isOpen_GLs hU' m
    · intro x₀ _
      refine ⟨Set.univ, Filter.univ_mem, Set.Icc (-T) T, isCompact_Icc, fun t ht y _ => ?_⟩
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hFN : NInv W₁ W₂ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') := by
    intro v hv' y hy
    simp only
    congr 1
    funext t
    rw [huN t v hv' y hy]
  have hint : ∀ x' ∈ GLs n, Integrable (fun t => ((g t : ℝ) : ℂ) • u t x') := by
    intro x' hx'
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := hU'.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨trivial, hx'⟩
      exact this
    · refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc fun t ht => ?_
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hcong : EqOn (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x'))
      (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) (GLs n) := by
    intro x' hx'
    simp only
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint x' hx')]
    congr 1
    funext t
    rw [map_smul]
  calc act μ E k (fun y => A y (f y)) x = act μ E k (fun y => A y (u 0 y)) x := by
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]
    _ = zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x')) x := h1
    _ = zOp w (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) x := zop_congr w hcong hx
    _ = A x (zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') x) :=
        zop_field hGC hGF hW A hA.1 hQ w _ hFs hFN hx
    _ = A x (act μ E k (u 0) x) := by rw [h2]
    _ = A x (act μ E k f x) := by
        congr 1
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]

end PositivityTheory.RgBcC.VC
