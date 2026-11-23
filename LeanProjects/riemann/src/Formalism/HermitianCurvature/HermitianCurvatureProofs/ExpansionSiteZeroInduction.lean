import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def SmoothOn (f : ℂ → ℂ) : Prop := ∀ n : ℕ, ContDiffOn ℝ n f {t | t ≠ 0}

theorem isOpen_ne_zero_complex : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne

theorem SmoothOn.diffAt {f : ℂ → ℂ} (hf : SmoothOn f) {t : ℂ} (ht : t ≠ 0) : DifferentiableAt ℝ f t := ((hf 1).contDiffAt (isOpen_ne.mem_nhds ht)).differentiableAt (by norm_num)

theorem SmoothOn.fderiv_apply {f : ℂ → ℂ} (hf : SmoothOn f) (v : ℂ) : SmoothOn (fun t => fderiv ℝ f t v) := by
  intro n
  have h1 : ContDiffOn ℝ n (fun y => fderiv ℝ f y) {t | t ≠ 0} :=
    (hf (n + 1)).fderiv_of_isOpen isOpen_ne (by push_cast; exact le_rfl)
  exact h1.clm_apply contDiffOn_const

theorem SmoothOn.wirt' {f : ℂ → ℂ} (hf : SmoothOn f) (b : Bool) : SmoothOn (CutSE.wirt b f) := by
  intro n
  unfold CutSE.wirt
  exact contDiffOn_const.mul ((hf.fderiv_apply 1 n).add (contDiffOn_const.mul (hf.fderiv_apply Complex.I n)))

theorem SmoothOn.wd {f : ℂ → ℂ} (hf : SmoothOn f) : ∀ bs : List Bool, SmoothOn (WD bs f)
  | [] => hf
  | b :: bs => (SmoothOn.wd hf bs).wirt' b

theorem wirt_congr {f g : ℂ → ℂ} {t : ℂ} (b : Bool) (h : f =ᶠ[𝓝 t] g) : CutSE.wirt b f t = CutSE.wirt b g t := by
  simp only [CutSE.wirt, h.fderiv_eq]

theorem wirt_add {f g : ℂ → ℂ} {t : ℂ} (b : Bool) (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    CutSE.wirt b (fun s => f s + g s) t = CutSE.wirt b f t + CutSE.wirt b g t := by
  have h : fderiv ℝ (fun s => f s + g s) t = fderiv ℝ f t + fderiv ℝ g t := fderiv_add hf hg
  simp only [CutSE.wirt, h, ContinuousLinearMap.add_apply]
  ring

theorem wirt_const_mul {f : ℂ → ℂ} {t : ℂ} (b : Bool) (e : ℂ) (hf : DifferentiableAt ℝ f t) :
    CutSE.wirt b (fun s => e * f s) t = e * CutSE.wirt b f t := by
  simp only [CutSE.wirt, fderiv_const_mul hf e, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem diff_listSum {ι : Type*} (L : List ι) (F : ι → ℂ → ℂ) {t : ℂ} (hF : ∀ i ∈ L, DifferentiableAt ℝ (F i) t) :
    DifferentiableAt ℝ (fun s => (L.map fun i => F i s).sum) t := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF i List.mem_cons_self).add (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))

theorem wirt_listSum {ι : Type*} (b : Bool) (L : List ι) (F : ι → ℂ → ℂ) {t : ℂ}
    (hF : ∀ i ∈ L, DifferentiableAt ℝ (F i) t) :
    CutSE.wirt b (fun s => (L.map fun i => F i s).sum) t = (L.map fun i => CutSE.wirt b (F i) t).sum := by
  induction L with
  | nil => simp [CutSE.wirt]
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hL : ∀ j ∈ L, DifferentiableAt ℝ (F j) t := fun j hj => hF j (List.mem_cons_of_mem _ hj)
    rw [wirt_add b (hF i List.mem_cons_self) (diff_listSum L F hL), ih hL]

section Num

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def IsNum (N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) : Prop :=
  ∀ a b, ∃ q : ℂ, N a b = algebraMap ℂ (Pr (RadSp k r z z' π π')) q

theorem isNum_one : IsNum (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) := by
  intro a b
  by_cases h : a = b
  · subst h
    exact ⟨1, by rw [Matrix.one_apply_eq, map_one]⟩
  · exact ⟨0, by rw [Matrix.one_apply_ne h, map_zero]⟩

theorem isNum_eU (s : S) (i j : Fin 2) : IsNum (eU s i j : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) := by
  intro a b
  by_cases h : a s = i ∧ b s = j ∧ ∀ c, c ≠ s → a c = b c
  · exact ⟨1, by simp only [eU, Matrix.of_apply, if_pos h, map_one]⟩
  · exact ⟨0, by simp only [eU, Matrix.of_apply, if_neg h, map_zero]⟩

theorem isNum_mul {M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))} (hM : IsNum M) (hN : IsNum N) : IsNum (M * N) := by
  choose qM hqM using hM
  choose qN hqN using hN
  intro a b
  exact ⟨∑ c, qM a c * qN c b, by simp [Matrix.mul_apply, hqM, hqN, map_sum, map_mul]⟩

theorem act_num_mem (K : Submodule ℂ (RadSp k r z z' π π')) {N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))} (hN : IsNum N)
    {v : Ix S → RadSp k r z z' π π'} (hv : ∀ b, v b ∈ K) : ∀ b, act N v b ∈ K := by
  intro b
  unfold act
  refine K.sum_mem fun c _ => ?_
  obtain ⟨q, hq⟩ := hN b c
  rw [hq]
  show (algebraMap ℂ (Module.End ℂ (RadSp k r z z' π π')) q) (v c) ∈ K
  rw [Module.algebraMap_end_apply]
  exact K.smul_mem q (hv c)

theorem act_one' (v : Ix S → RadSp k r z z' π π') : act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v = v := by
  funext b
  unfold act
  rw [Finset.sum_eq_single b]
  · simp only [Matrix.one_apply_eq]
    rfl
  · intro c _ hc
    rw [Matrix.one_apply_ne (Ne.symm hc)]
    rfl
  · intro h
    exact absurd (Finset.mem_univ b) h

end Num

theorem sum_fin_list {α : Type*} (L : List α) (g : α → ℂ) : ∑ i : Fin L.length, g (L.get i) = (L.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  have h : (fun i : Fin L.length => g (L.get i)) = g ∘ L.get := rfl
  rw [h, ← List.map_ofFn, List.ofFn_get]

section Slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem comm_eU_io (a : S) (p q : Fin 2) (y : A) : Commute (eU a p q : SlopeTestRemainingChoices S A) (io y) := by
  ext x w
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem comm_eU_vlet (σ : Site A) (le : Letter ℂ S) {a : S} (ha : le.intersection_update_fsHerm_neg_one ≠ a) (i j : Fin 2) :
    Commute (eU a i j : SlopeTestRemainingChoices S A) (vlet σ le) := by
  have L : ∀ (a s : S), s ≠ a → ∀ (i j p q : Fin 2) (x y : Ix S),
      (((eU a i j : SlopeTestRemainingChoices S A) * (eU s p q : SlopeTestRemainingChoices S A)) : SlopeTestRemainingChoices S A) x y =
        if x a = i ∧ y a = j ∧ x s = p ∧ y s = q ∧ ∀ b, b ≠ a → b ≠ s → x b = y b then 1 else 0 := by
    intro a s hs i j p q x y
    have hsa : a ≠ s := Ne.symm hs
    rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x a j)]
    · simp only [eU, Matrix.of_apply, Function.update_self, Function.update_of_ne hs]
      by_cases h1 : x a = i
      · have e1 : (∀ b, b ≠ a → x b = Function.update x a j b) := fun b hb => by
          rw [Function.update_of_ne hb]
        rw [if_pos ⟨h1, trivial, e1⟩, one_mul]
        by_cases h2 : y a = j ∧ x s = p ∧ y s = q ∧ ∀ b, b ≠ a → b ≠ s → x b = y b
        · obtain ⟨h2a, h2b, h2c, h2d⟩ := h2
          have e2 : ∀ b, b ≠ s → Function.update x a j b = y b := by
            intro b hb
            by_cases hba : b = a
            · subst hba; rw [Function.update_self, h2a]
            · rw [Function.update_of_ne hba]; exact h2d b hba hb
          rw [if_pos ⟨h2b, h2c, e2⟩, if_pos ⟨h1, h2a, h2b, h2c, h2d⟩]
        · rw [if_neg (fun h => h2 ⟨?_, h.1, h.2.1, fun b hba hbs => ?_⟩), if_neg (fun h => h2 h.2)]
          · have := h.2.2 a hsa
            rw [Function.update_self] at this
            exact this.symm
          · have := h.2.2 b hbs
            rw [Function.update_of_ne hba] at this
            exact this
      · rw [if_neg (fun h => h1 h.1), zero_mul, if_neg (fun h => h1 h.1)]
    · intro w _ hw
      simp only [eU, Matrix.of_apply]
      rw [if_neg, zero_mul]
      rintro ⟨_, hwa, hwb⟩
      apply hw
      funext b
      by_cases hba : b = a
      · subst hba; rw [Function.update_self, hwa]
      · rw [Function.update_of_ne hba]; exact (hwb b hba).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hee : ∀ s : S, s ≠ a → ∀ p q : Fin 2, Commute (eU a i j : SlopeTestRemainingChoices S A) (eU s p q) := by
    intro s hs p q
    ext x y
    rw [L a s hs i j p q x y, L s a (Ne.symm hs) p q i j x y]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h3, h4, h1, h2, fun b hb1 hb2 => h5 b hb2 hb1⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h3, h4, h1, h2, fun b hb1 hb2 => h5 b hb2 hb1⟩
  unfold vlet ins lift0
  refine Commute.sum_right _ _ _ fun p _ => Commute.sum_right _ _ _ fun q _ => ?_
  exact (hee le.intersection_update_fsHerm_neg_one ha p q).mul_right (comm_eU_io a i j _)

theorem comm_eU_bT (σ : Site A) {a : S} (i j : Fin 2) : ∀ w : List (Letter ℂ S), a ∉ w.map Letter.intersection_update_fsHerm_neg_one →
    Commute (eU a i j : SlopeTestRemainingChoices S A) (bT σ w)
  | [], _ => Commute.one_right _
  | le :: w, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show Commute (eU a i j : SlopeTestRemainingChoices S A) (vlet σ le * bT σ w)
    exact (comm_eU_vlet σ le (Ne.symm h.1) i j).mul_right (comm_eU_bT σ i j w h.2)

end Slots

theorem expansion_site_zero_induction : ExpansionByLetterInduction := by
  intro hS hO hB
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  set Cl := ClsE S P z z' π π' X L st l0 D l with hCl
  set σ := site L l with hσ
  have hsm : ∀ u v : Ix S → RadSp P.k P.r z z' π π', (∀ b, u b ∈ Cl) → (∀ b, v b ∈ Cl) →
      SmoothOn (Dens μ l u v c) :=
    fun u v hu hv => (hS Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl u v hu hv c hc).1
  have hBl := hB Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl
  have hbT : ∀ (w' : List (Letter ℂ S)) (u : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ Cl) →
      ∀ b, act (bT σ w') u b ∈ Cl := by
    intro w'
    induction w' with
    | nil => intro u hu b; rw [show bT σ ([] : List (Letter ℂ S)) = 1 from rfl, act_one']; exact hu b
    | cons le w' ih =>
      intro u hu b
      rw [show bT σ (le :: w') = vlet σ le * bT σ w' from rfl, act_mul]
      exact (hBl _ (ih u hu)).1 le b
  have hibT : ∀ (w' : List (Letter ℂ S)) (u : Ix S → RadSp P.k P.r z z' π π'), (∀ b, u b ∈ Cl) →
      ∀ b, act (ibT σ w') u b ∈ Cl := by
    intro w'
    induction w' with
    | nil => intro u hu b; rw [show ibT σ ([] : List (Letter ℂ S)) = 1 from rfl, act_one']; exact hu b
    | cons le w' ih =>
      intro u hu b
      rw [show ibT σ (le :: w') = ivlet σ le * ibT σ w' from rfl, act_mul]
      exact (hBl _ (ih u hu)).2.1 le b
  have gen : ∀ w' : List (Letter ℂ S), (w'.map Letter.intersection_update_fsHerm_neg_one).Nodup → (∀ le ∈ w', le.pt.im = 0) →
      ∀ u v : Ix S → RadSp P.k P.r z z' π π', (∀ b, u b ∈ Cl) → (∀ b, v b ∈ Cl) →
      ∃ rest : List (ℂ × List Bool × SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))),
        (∀ τ ∈ rest, τ.2.1 ≠ [] ∧ τ.2.1.length ≤ w'.length ∧ IsNum τ.2.2) ∧
        ∀ t, t ≠ 0 → Dens μ l (act (ibT σ w') u) (act (bT σ w') v) c t =
          Dens μ l u v c t + (rest.map fun τ => τ.1 * WD τ.2.1 (Dens μ l u (act τ.2.2 v) c) t).sum := by
    intro w'
    induction w' with
    | nil =>
      intro _ _ u v _ _
      refine ⟨[], by simp, fun t _ => ?_⟩
      simp only [List.map_nil, List.sum_nil, add_zero]
      rw [show ibT σ ([] : List (Letter ℂ S)) = 1 from rfl, show bT σ ([] : List (Letter ℂ S)) = 1 from rfl,
        act_one', act_one']
    | cons le w' ih =>
      intro hnd hre u v hu hv
      have hnd' : le.intersection_update_fsHerm_neg_one ∉ w'.map Letter.intersection_update_fsHerm_neg_one ∧ (w'.map Letter.intersection_update_fsHerm_neg_one).Nodup := by
        simpa using hnd
      obtain ⟨e, bb, i, j, hOL⟩ :=
        hO Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl le (hre le List.mem_cons_self)
      have hre' : ∀ le' ∈ w', le'.pt.im = 0 := fun le' h => hre le' (List.mem_cons_of_mem _ h)
      have hev : ∀ b, act (eU le.intersection_update_fsHerm_neg_one i j) v b ∈ Cl := (hBl v hv).2.2 le.intersection_update_fsHerm_neg_one i j
      obtain ⟨rest1, hr1, h1⟩ := ih hnd'.2 hre' u v hu hv
      obtain ⟨rest2, hr2, h2⟩ := ih hnd'.2 hre' u (act (eU le.intersection_update_fsHerm_neg_one i j) v) hu hev
      refine ⟨rest1 ++ (e, [bb], eU le.intersection_update_fsHerm_neg_one i j) ::
        rest2.map (fun τ => (e * τ.1, bb :: τ.2.1, τ.2.2 * eU le.intersection_update_fsHerm_neg_one i j)), ?_, ?_⟩
      · intro τ hτ
        simp only [List.mem_append, List.mem_cons, List.mem_map] at hτ
        rcases hτ with hτ | hτ | ⟨τ', hτ', rfl⟩
        · obtain ⟨a1, a2, a3⟩ := hr1 τ hτ
          exact ⟨a1, by simp only [List.length_cons]; omega, a3⟩
        · subst hτ
          exact ⟨by simp, by simp, isNum_eU _ _ _⟩
        · obtain ⟨a1, a2, a3⟩ := hr2 τ' hτ'
          exact ⟨by simp, by simp only [List.length_cons]; omega, isNum_mul a3 (isNum_eU _ _ _)⟩
      · intro t ht
        have hU' : ∀ b, act (ibT σ w') u b ∈ Cl := hibT w' u hu
        have hV' : ∀ b, act (bT σ w') v b ∈ Cl := hbT w' v hv
        have step1 : Dens μ l (act (ibT σ (le :: w')) u) (act (bT σ (le :: w')) v) c t =
            Dens μ l (act (ivlet σ le) (act (ibT σ w') u)) (act (vlet σ le) (act (bT σ w') v)) c t := by
          rw [show ibT σ (le :: w') = ivlet σ le * ibT σ w' from rfl,
            show bT σ (le :: w') = vlet σ le * bT σ w' from rfl, act_mul, act_mul]
        have hcomm : act (eU le.intersection_update_fsHerm_neg_one i j) (act (bT σ w') v) = act (bT σ w') (act (eU le.intersection_update_fsHerm_neg_one i j) v) := by
          rw [← act_mul, ← act_mul, (comm_eU_bT σ i j w' hnd'.1).eq]
        have hevt : Dens μ l (act (ibT σ w') u) (act (eU le.intersection_update_fsHerm_neg_one i j) (act (bT σ w') v)) c =ᶠ[𝓝 t]
            (fun s => Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one i j) v) c s + (rest2.map fun τ =>
              τ.1 * WD τ.2.1 (Dens μ l u (act τ.2.2 (act (eU le.intersection_update_fsHerm_neg_one i j) v)) c) s).sum) := by
          filter_upwards [isOpen_ne_zero_complex.mem_nhds ht] with s hs
          rw [hcomm]
          exact h2 s hs
        have hd0 : DifferentiableAt ℝ (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one i j) v) c) t := (hsm u _ hu hev).diffAt ht
        have hdτ : ∀ τ ∈ rest2, DifferentiableAt ℝ
            (fun s => τ.1 * WD τ.2.1 (Dens μ l u (act τ.2.2 (act (eU le.intersection_update_fsHerm_neg_one i j) v)) c) s) t := by
          intro τ hτ
          exact (((hsm u _ hu (act_num_mem Cl (hr2 τ hτ).2.2 hev)).wd τ.2.1).diffAt ht).const_mul τ.1
        have hterm : ∀ τ ∈ rest2,
            CutSE.wirt bb (fun s => τ.1 * WD τ.2.1 (Dens μ l u (act τ.2.2 (act (eU le.intersection_update_fsHerm_neg_one i j) v)) c) s) t =
              τ.1 * WD (bb :: τ.2.1) (Dens μ l u (act (τ.2.2 * eU le.intersection_update_fsHerm_neg_one i j) v) c) t := by
          intro τ hτ
          rw [wirt_const_mul bb τ.1 (((hsm u _ hu (act_num_mem Cl (hr2 τ hτ).2.2 hev)).wd τ.2.1).diffAt ht), act_mul]
          rfl
        rw [step1, hOL _ _ hU' hV' c hc t ht, h1 t ht, wirt_congr bb hevt,
          wirt_add bb hd0 (diff_listSum rest2 _ hdτ), wirt_listSum bb rest2 _ hdτ, List.map_congr_left hterm]
        simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
        rw [mul_add, ← List.sum_map_mul_left]
        have hW1 : WD [bb] (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one i j) v) c) t =
            CutSE.wirt bb (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one i j) v) c) t := rfl
        rw [hW1]
        simp only [mul_assoc]
        ring
  have hnd : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup := (good_of_adm st w hw.1).1
  have hre : ∀ le ∈ w, le.pt.im = 0 := fun le h => (hw.2.1 le h).1
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  have hbase : ∀ Φ ∈ base0 S P z z' π π' L st l0 D, Φ ∈ Cl := fun Φ h =>
    Submodule.subset_span ⟨[], Φ, h, by simp⟩
  have hX : ∀ b, act (RRi L st l.castSucc w) x b ∈ Cl := by
    intro b
    apply hbase
    simp only [act]
    refine Submodule.sum_mem _ fun b' _ => ?_
    apply Submodule.mem_sup_right
    refine Submodule.subset_span ⟨w, hw, b, b', x b', ?_, ?_⟩
    · have := hx b'
      rw [hl0] at this
      exact this
    · rw [hl0]
  have hy' : ∀ b, y b ∈ Cl := fun b => hbase _ (Submodule.mem_sup_left (by have := hy b; rw [hl0] at this; exact this))
  obtain ⟨rest, hr, hE⟩ := gen w hnd hre _ y hX hy'
  generalize hterms : (((1 : ℂ), ([] : List Bool), (1 : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) :: rest :
    List (ℂ × List Bool × SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) = terms
  have key : ∀ τ ∈ terms, τ.2.1.length ≤ w.length ∧ IsNum τ.2.2 := by
    rw [← hterms]
    intro τ hτ
    rcases List.mem_cons.mp hτ with h | h
    · rw [h]; exact ⟨by simp, isNum_one⟩
    · exact ⟨(hr _ h).2.1, (hr _ h).2.2⟩
  have hmem : ∀ i : Fin terms.length, (terms.get i).2.1.length ≤ w.length ∧ IsNum (terms.get i).2.2 :=
    fun i => key _ (List.get_mem terms i)
  refine ⟨terms.length, fun i => (terms.get i).1, fun i => (terms.get i).2.1, fun i => act (terms.get i).2.2 y,
    fun i => (hmem i).1, fun i b => act_num_mem _ (hmem i).2 hy b, fun t ht => ?_, ?_⟩
  · rw [sum_fin_list terms (fun τ => τ.1 * WD τ.2.1 (Dens μ l (act (RRi L st l.castSucc w) x) (act τ.2.2 y) c) t)]
    show Dens μ l (act (ibT σ w) (act (RRi L st l.castSucc w) x)) (act (bT σ w) y) c t = _
    rw [hE t ht, ← hterms, List.map_cons, List.sum_cons, act_one']
    simp only [one_mul]
    rfl
  · rw [sum_fin_list terms (fun τ => τ.1 * (if τ.2.1 = [] then form μ l.castSucc (act (RRi L st l.castSucc w) x)
      (act τ.2.2 y) c else 0))]
    rw [← hterms, List.map_cons, List.sum_cons, act_one']
    have h0 : (rest.map fun τ => τ.1 * (if τ.2.1 = [] then form μ l.castSucc (act (RRi L st l.castSucc w) x)
        (act τ.2.2 y) c else 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro q hq
      obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hq
      rw [if_neg (hr τ hτ).1, mul_zero]
    rw [h0, add_zero, if_pos rfl, one_mul]
    rfl

end Formalism.FourierDecayAlt.P.CutSE
