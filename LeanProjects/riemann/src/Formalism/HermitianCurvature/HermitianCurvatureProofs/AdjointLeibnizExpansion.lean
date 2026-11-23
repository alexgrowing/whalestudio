import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxI

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section hsadj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def hsVecL : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by
    unfold hsVec
    ext i
    simp
  map_smul' c A := by
    unfold hsVec
    ext i
    simp

theorem hsVec_injective : Function.Injective (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => ?_
  have := congrFun (congrArg WithLp.ofLp h) i
  simpa [hsVec] using this

theorem hsVec_surjective :
    Function.Surjective (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  intro v
  refine ⟨∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (WithLp.ofLp v i), ?_⟩
  first
  | (ext j
     simp [hsVec, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, OrthonormalBasis.inner_eq_ite,
       ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq'])
  | (apply WithLp.ofLp_injective
     funext j
     simp [hsVec, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, OrthonormalBasis.inner_eq_ite,
       ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq'])

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearEquiv.ofBijective hsVecL ⟨hsVec_injective, hsVec_surjective⟩

theorem hsE_apply (A : Wq →L[ℂ] Wp) : hsE A = hsVec A := rfl

def hsAdj (B : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap ((hsE.symm.toLinearMap ∘ₗ
    LinearMap.adjoint (hsE.toLinearMap ∘ₗ B.toLinearMap ∘ₗ hsE.symm.toLinearMap)) ∘ₗ hsE.toLinearMap)

theorem hsAdj_spec (B : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A C : Wq →L[ℂ] Wp) :
    hsInner (B A) C = hsInner A (hsAdj B C) := by
  simp only [hsInner, ← hsE_apply]
  unfold hsAdj
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.adjoint_inner_left, ContinuousLinearMap.coe_coe,
    LinearEquiv.symm_apply_apply]

end hsadj

section calculus1

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_RdV' {m : ℕ∞} {UU : Set (Mat k r)} {f : Mat k r → E} {X : Mat k r} (hX : inLie k r X)
    (h : CkOn (m + 1) UU f) : CkOn m UU (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun x => fderiv ℝ f' x (x * X), hU, hgU, ?_, ?_⟩
  · have h1 := hf'.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hU (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ f' x :=
      (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    exact (B5.hasDerivAt_of_ext hU hx hxG hX hd he).deriv

theorem ckOn_Rw' {UU : Set (Mat k r)} {f : Mat k r → E} {N : ℕ} (h : CkOn (N : ℕ∞) UU f) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : CkOn (m : ℕ∞) UU (Rw w f) := by
  have key : ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ m : ℕ, m + w.length ≤ N →
      CkOn (m : ℕ∞) UU (Rw w f) := by
    intro w
    induction w with
    | nil =>
      intro _ m hle
      intro g₀ hg
      obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg
      exact ⟨U, f', hU, hgU, hf'.of_le (by norm_cast <;> simpa using hle), hff⟩
    | cons X w ih =>
      intro hw m hle
      have hX : inLie k r X := hw X (by simp)
      have h1 := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
      have h2 : CkOn ((m : ℕ∞) + 1) UU (Rw w f) := by exact_mod_cast h1
      exact ckOn_RdV' hX h2
  exact key w hw m hle

theorem ckOn_Rw_top' {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn ⊤ UU f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ UU (Rw w f) := by
  intro w hw
  induction w with
  | nil => exact h
  | cons X w ih =>
    have hX : inLie k r X := hw X (by simp)
    have h1 := ih (fun Y hY => hw Y (by simp [hY]))
    have h2 : CkOn ((⊤ : ℕ∞) + 1) UU (Rw w f) := by simpa using h1
    exact ckOn_RdV' hX h2

theorem rdV_hasDerivAt' {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn 1 UU f) {g X : Mat k r} (hg : g ∈ UU)
    (hgG : g ∈ GV k r) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  exact (B5.hasDerivAt_of_ext hU hgU hgG hX hd he).differentiableAt.hasDerivAt

theorem hasDerivAt_list_sum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : List ι) (g : ι → ℝ → F)
    (g' : ι → F) {t : ℝ} (h : ∀ i ∈ L, HasDerivAt (g i) (g' i) t) :
    HasDerivAt (fun s => (L.map fun i => g i s).sum) (L.map g').sum t := by
  induction L with
  | nil => simpa using hasDerivAt_const t (0 : F)
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

end calculus1

def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | X :: w => (splits w).map (fun uv => (X :: uv.1, uv.2)) ++ (splits w).map (fun uv => (uv.1, X :: uv.2))

theorem splits_mem {α : Type*} : ∀ (w : List α), ∀ uv ∈ splits w,
    (∀ X ∈ uv.1, X ∈ w) ∧ (∀ X ∈ uv.2, X ∈ w) ∧ uv.2.length ≤ w.length
  | [], uv, h => by simp [splits] at h; subst h; simp
  | X :: w, uv, h => by
    simp only [splits, List.mem_append, List.mem_map] at h
    rcases h with ⟨uv', h', rfl⟩ | ⟨uv', h', rfl⟩
    · obtain ⟨a, b, c⟩ := splits_mem w uv' h'
      refine ⟨?_, fun Y hY => List.mem_cons_of_mem _ (b Y hY), by simp; omega⟩
      intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (a Y hY)
    · obtain ⟨a, b, c⟩ := splits_mem w uv' h'
      refine ⟨fun Y hY => List.mem_cons_of_mem _ (a Y hY), ?_, by simp; omega⟩
      intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (b Y hY)

theorem splits_full {α : Type*} : ∀ (w : List α), (([] : List α), w) ∈ splits w
  | [] => by simp [splits]
  | X :: w => by
    simp only [splits, List.mem_append, List.mem_map]
    exact Or.inr ⟨([], w), splits_full w, rfl⟩

section leib

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_leib (z z' : Fin (2 * r + k + 1) → ℂ) (A : Mat k r → (E →L[ℂ] E)) (f : Mat k r → E) (N : ℕ)
    (hA : CkOn ⊤ (Om k r z z') A) (hf : CkOn (N : ℕ∞) (Om k r z z') f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → w.length ≤ N → ∀ x ∈ Om k r z z',
      Rw w (fun y => A y (f y)) x = ((splits w).map fun uv => Rw uv.1 A x (Rw uv.2 f x)).sum := by
  intro w
  induction w with
  | nil => intro _ _ x _; simp [splits, Rw]
  | cons X w ih =>
    intro hw hlen x hx
    have hwL : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hX : inLie k r X := hw X List.mem_cons_self
    have hlen' : w.length + 1 ≤ N := by simpa using hlen
    have hloc := PositiveOrbitOpen.rdV_local (f₁ := Rw w (fun y => A y (f y)))
      (f₂ := fun y => ((splits w).map fun uv => Rw uv.1 A y (Rw uv.2 f y)).sum) (PositiveOrbitOpen.omPlus_open z z')
      (fun y hy hyG => ih hwL (by omega) y ⟨hyG, hy⟩) hX x hx.2 hx.1
    change RdV X (Rw w (fun y => A y (f y))) x = _
    rw [hloc]
    have hd : HasDerivAt
        (fun t : ℝ => ((splits w).map fun uv =>
          Rw uv.1 A (x * NormedSpace.exp ((t : ℂ) • X)) (Rw uv.2 f (x * NormedSpace.exp ((t : ℂ) • X)))).sum)
        (((splits w).map fun uv => RdV X (Rw uv.1 A) x (Rw uv.2 f x) + Rw uv.1 A x (RdV X (Rw uv.2 f) x)).sum) 0 := by
      apply hasDerivAt_list_sum (splits w)
        (fun uv t => Rw uv.1 A (x * NormedSpace.exp ((t : ℂ) • X)) (Rw uv.2 f (x * NormedSpace.exp ((t : ℂ) • X))))
      intro uv huv
      obtain ⟨h1m, h2m, h2l⟩ := splits_mem w uv huv
      have h1 : HasDerivAt (fun t : ℝ => Rw uv.1 A (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X (Rw uv.1 A) x) 0 :=
        rdV_hasDerivAt' (B5.ckOn_mono le_top (ckOn_Rw_top' hA uv.1 fun Y hY => hwL Y (h1m Y hY))) hx hx.1 hX
      have h2 : HasDerivAt (fun t : ℝ => Rw uv.2 f (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X (Rw uv.2 f) x) 0 := by
        have hc := ckOn_Rw' hf uv.2 (fun Y hY => hwL Y (h2m Y hY)) 1 (by omega)
        exact rdV_hasDerivAt' (by exact_mod_cast hc) hx hx.1 hX
      have h1' : HasDerivAt (fun t : ℝ => ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
          (Rw uv.1 A (x * NormedSpace.exp ((t : ℂ) • X))))
          (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ (RdV X (Rw uv.1 A) x)) 0 :=
        (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
      have h3 := h1'.clm_apply h2
      convert h3 using 1
      all_goals first | rfl | (rw [B5.curve_zero]; rfl)
    change deriv (fun t : ℝ => ((splits w).map fun uv =>
          Rw uv.1 A (x * NormedSpace.exp ((t : ℂ) • X)) (Rw uv.2 f (x * NormedSpace.exp ((t : ℂ) • X)))).sum) 0 = _
    rw [hd.deriv]
    simp only [splits, List.map_append, List.map_map, List.sum_append, List.sum_map_add]
    rfl

end leib

section adjop

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lieOr (v : List (Mat k r)) : List (Mat k r) := by
  classical exact if ∀ X ∈ v, inLie k r X then v else []

theorem lieOr_lie (v : List (Mat k r)) : ∀ X ∈ lieOr v, inLie k r X := by
  unfold lieOr
  split_ifs with h
  · exact h
  · simp

theorem lieOr_eq {v : List (Mat k r)} (h : ∀ X ∈ v, inLie k r X) : lieOr v = v := by
  unfold lieOr
  rw [if_pos h]

theorem lieOr_len (v : List (Mat k r)) : (lieOr v).length ≤ v.length := by
  unfold lieOr
  split_ifs <;> simp

def adjTerm (T : DTerm k r Wp Wq) (uv : List (Mat k r) × List (Mat k r)) : DTerm k r Wp Wq where
  coef := fun g => ((-1 : ℂ) ^ T.word.length) • Rw uv.1 T.coefAdj g
  coefAdj := fun g => hsAdj (((-1 : ℂ) ^ T.word.length) • Rw uv.1 T.coefAdj g)
  word := lieOr uv.2
  word_lie := lieOr_lie uv.2
  adj_id := fun _ A B => hsAdj_spec _ A B

def adjOp (Θ : DiffOp k r Wp Wq) : DiffOp k r Wp Wq :=
  Θ.flatMap fun T => (splits T.word.reverse).map (adjTerm T)

theorem foldr_max_le_iff (L : List ℕ) (n : ℕ) : L.foldr max 0 ≤ n ↔ ∀ x ∈ L, x ≤ n := by
  induction L with
  | nil => simp
  | cons x L ih => simp [max_le_iff, ih]

theorem adjOp_order (Θ : DiffOp k r Wp Wq) : opOrder (adjOp Θ) = opOrder Θ := by
  have key : ∀ (L : List ℕ) (x : ℕ), x ∈ L → x ≤ L.foldr max 0 :=
    fun L x hx => (foldr_max_le_iff L _).1 le_rfl x hx
  unfold opOrder
  apply le_antisymm
  · rw [foldr_max_le_iff]
    intro x hx
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hx
    unfold adjOp at hT'
    obtain ⟨T, hT, hT''⟩ := List.mem_flatMap.1 hT'
    obtain ⟨uv, huv, rfl⟩ := List.mem_map.1 hT''
    calc (adjTerm T uv).word.length = (lieOr uv.2).length := rfl
      _ ≤ uv.2.length := lieOr_len _
      _ ≤ T.word.reverse.length := (splits_mem _ uv huv).2.2
      _ = T.word.length := by simp
      _ ≤ _ := key _ _ (List.mem_map.2 ⟨T, hT, rfl⟩)
  · rw [foldr_max_le_iff]
    intro x hx
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    have hlie : ∀ X ∈ T.word.reverse, inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
    have hmem : adjTerm T ([], T.word.reverse) ∈ adjOp Θ := by
      unfold adjOp
      exact List.mem_flatMap.2 ⟨T, hT, List.mem_map.2 ⟨_, splits_full _, rfl⟩⟩
    calc T.word.length = (adjTerm T ([], T.word.reverse)).word.length := by
          show T.word.length = (lieOr T.word.reverse).length
          rw [lieOr_eq hlie, List.length_reverse]
      _ ≤ _ := key _ _ (List.mem_map.2 ⟨_, hmem, rfl⟩)

theorem adjOp_apply (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (Om k r D.z D.z') Θ)
    (f : Mat k r → (Wq →L[ℂ] Wp)) (hf : CkOn (opOrder Θ : ℕ∞) (Om k r D.z D.z') f) (g : Mat k r)
    (hg : g ∈ Om k r D.z D.z') : opApply (adjOp Θ) f g = opAdj Θ f g := by
  have term : ∀ T ∈ Θ, (((splits T.word.reverse).map (adjTerm T)).map
      fun T' : DTerm k r Wp Wq => T'.coef g (Rw T'.word f g)).sum =
        ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (f x)) g := by
    intro T hT
    have hlen : T.word.reverse.length ≤ opOrder Θ := by
      rw [List.length_reverse]
      exact (foldr_max_le_iff (Θ.map fun T => T.word.length) (opOrder Θ)).1 le_rfl T.word.length
        (List.mem_map.2 ⟨T, hT, rfl⟩)
    have hlie : ∀ X ∈ T.word.reverse, inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
    rw [rw_leib D.z D.z' T.coefAdj f (opOrder Θ) (hS T hT).2 hf T.word.reverse hlie hlen g hg, List.smul_sum,
      List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro uv huv
    have hsub : ∀ X ∈ uv.2, inLie k r X := fun X hX => hlie X ((splits_mem _ uv huv).2.1 X hX)
    simp only [Function.comp_apply, adjTerm, lieOr_eq hsub, ContinuousLinearMap.smul_apply]
  have gen : ∀ L : DiffOp k r Wp Wq, (∀ T ∈ L, T ∈ Θ) →
      ((L.flatMap fun T => (splits T.word.reverse).map (adjTerm T)).map
        fun T' : DTerm k r Wp Wq => T'.coef g (Rw T'.word f g)).sum =
      (L.map fun T => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (f x)) g).sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons T L ih =>
      intro hL
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [term T (hL T (by simp)), ih (fun T' h' => hL T' (by simp [h']))]
      simp
  unfold opApply opAdj adjOp
  exact gen Θ (fun T h => h)

end adjop

end Formalism.FourierDecayAlt.P.JFxI

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem adjoint_leibniz_expansion : Formalism.FourierDecayAlt.P.JFxI.AdjLeibniz := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hS
  exact ⟨JFxI.adjOp Θ, JFxI.adjOp_order Θ, fun f hf g hg => JFxI.adjOp_apply D Θ hS f hf g hg⟩

end Formalism.FourierDecayAlt.P
