import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure Tm (k r : ℕ) where
  j : ℕ
  ws : Fin j → List (Bool × Mat k r)

variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

def tval (Ψ : V → E') (F : Mat k r → V) (t : Tm k r) (g : Mat k r) : E' :=
  iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)

def tnext (x : Bool × Mat k r) (t : Tm k r) : List (Tm k r) :=
  ⟨t.j + 1, Fin.cons [x] t.ws⟩ :: List.ofFn fun i : Fin t.j => (⟨t.j, Function.update t.ws i (x :: t.ws i)⟩ : Tm k r)

theorem hasDerivAt_list_sum {ι : Type} (l : List ι) (f : ι → ℝ → E') (f' : ι → E')
    (h : ∀ i ∈ l, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun s => (l.map fun i => f i s).sum) (l.map f').sum 0 := by
  induction l with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E')
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem list_sum_flatMap {ι κ : Type} (l : List ι) (f : ι → List κ) (g : κ → E') :
    ((l.flatMap f).map g).sum = (l.map fun i => ((f i).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem tval_hasDerivAt {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hF : CkOn ⊤ (U ∩ GV k r) F) {x : Bool × Mat k r} (hx : inLie k r x.2)
    (t : Tm k r) (hws : ∀ i, ∀ y ∈ t.ws i, inLie k r y.2) {g : Mat k r} (hgU : g ∈ U) (hg : g ∈ GV k r) :
    HasDerivAt (fun s : ℝ => tval Ψ F t (crv x g s)) (((tnext x t).map fun t' => tval Ψ F t' g).sum) 0 := by
  have hg' : g ∈ U ∩ GV k r := ⟨hgU, hg⟩
  have hF1 : ∀ n : ℕ∞, CkOn n (U ∩ GV k r) F := fun n => CkOn_mono le_top hF
  have hA : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ t.j Ψ (F (crv x g s)))
      (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g) (Dx x F g)) 0 := by
    have h1 := CkOn_diff hx (hF1 1) hg' hg
    have hlt : ((t.j : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)
    have h2 : HasFDerivAt (iteratedFDeriv ℝ t.j Ψ) (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g))
        (F (crv x g 0)) := by
      rw [crv_zero]
      exact ((hΨ.differentiable_iteratedFDeriv hlt) (F g)).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hv : ∀ i, HasDerivAt (fun s : ℝ => Dw (t.ws i) F (crv x g s)) (Dw (x :: t.ws i) F g) 0 := by
    intro i
    exact CkOn_diff hx (CkOn_Dw (hws i) (hF1 _)) hg' hg
  have hD := (hA.hasFDerivAt).continuousMultilinearMap_apply (fun i => (hv i).hasFDerivAt)
  refine hD.hasDerivAt.congr_deriv ?_
  simp only [crv_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul, ContinuousMultilinearMap.apply_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [tnext, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  funext l
  by_cases h : l = i
  · subst h
    simp
  · simp [Function.update_apply, h]

theorem expand {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hU : IsOpen U) (hF : CkOn ⊤ (U ∩ GV k r) F) :
    ∀ w : List (Bool × Mat k r), (∀ y ∈ w, inLie k r y.2) →
      ∃ ts : List (Tm k r), ts.length ≤ (w.length + 1).factorial ∧
        (∀ t ∈ ts, t.j ≤ w.length ∧ (∑ i, (t.ws i).length) = w.length ∧ ∀ i, (t.ws i).Sublist w) ∧
        ∀ g ∈ U, g ∈ GV k r → Dw w (fun g => Ψ (F g)) g = (ts.map fun t => tval Ψ F t g).sum := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨[⟨0, Fin.elim0⟩], by simp, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨le_rfl, by simp, fun i => i.elim0⟩
    · intro g _ _
      simp [tval, Dw]
  | cons x w ih =>
    intro hw
    obtain ⟨ts, hlen, hts, hval⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx : inLie k r x.2 := hw x (by simp)
    refine ⟨ts.flatMap (tnext x), ?_, ?_, ?_⟩
    · have hl : ∀ t ∈ ts, (tnext x t).length ≤ w.length + 1 := by
        intro t ht
        simp only [tnext, List.length_cons, List.length_ofFn]
        have := (hts t ht).1
        omega
      have hs : (ts.map fun t => (tnext x t).length).sum ≤ (ts.map fun _ => w.length + 1).sum :=
        List.sum_le_sum hl
      rw [List.map_const', List.sum_replicate, smul_eq_mul] at hs
      rw [List.length_flatMap, List.length_cons, Nat.factorial_succ]
      calc _ ≤ ts.length * (w.length + 1) := hs
        _ ≤ (w.length + 1).factorial * (w.length + 1 + 1) := Nat.mul_le_mul hlen (by omega)
        _ = (w.length + 1 + 1) * (w.length + 1).factorial := Nat.mul_comm _ _
    · intro t' ht'
      obtain ⟨t, ht, ht'⟩ := List.mem_flatMap.mp ht'
      obtain ⟨hj, hsum, hsub⟩ := hts t ht
      simp only [tnext, List.mem_cons, List.mem_ofFn] at ht'
      rcases ht' with rfl | ⟨i, rfl⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.length_cons, List.length_nil, hsum]
          omega
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp
          · simpa using (hsub i).cons x
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · have e : ∀ l, (Function.update t.ws i (x :: t.ws i) l).length = (t.ws l).length + if l = i then 1 else 0 := by
            intro l
            by_cases h : l = i
            · subst h
              simp
            · simp [Function.update_apply, h]
          simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsum,
            List.length_cons]
        · intro l
          by_cases h : l = i
          · simpa [h] using (hsub i).cons₂ x
          · simpa [Function.update_apply, h] using (hsub l).cons x
    · intro g hgU hg
      show Dx x (Dw w (fun g => Ψ (F g))) g = _
      rw [Dx_eq]
      have hev : Filter.EventuallyEq (nhds (0 : ℝ)) (fun s : ℝ => Dw w (fun g => Ψ (F g)) (crv x g s))
          (fun s => (ts.map fun t => tval Ψ F t (crv x g s)).sum) := by
        filter_upwards [crv_ev (x := x) hU hgU] with s hs
        exact hval _ hs (crv_mem hx hg s)
      rw [hev.deriv_eq, list_sum_flatMap]
      exact (hasDerivAt_list_sum ts (fun t s => tval Ψ F t (crv x g s))
        (fun t => ((tnext x t).map fun t' => tval Ψ F t' g).sum)
        (fun t ht => tval_hasDerivAt hΨ hF hx t
          (fun i y hy => hw y (List.mem_cons_of_mem _ (((hts t ht).2.2 i).subset hy))) hgU hg)).deriv

theorem chain_bound_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd
  intro k r V E' _ _ _ _ _ Ψ hΨ F U K hU hF hKU hKG Bg hBg hyp m
  classical
  obtain ⟨C0, hC0⟩ := hyp 0
  have hFb : ∀ g ∈ K, ‖F g‖ ≤ C0 := by
    intro g hg
    have := hC0 [] [] (by simp) (by simp) (by simp) g hg
    simpa [dLR, Rw] using this
  have hΨb : ∀ j : ℕ, ∃ B, ∀ y : V, ‖y‖ ≤ C0 → ‖iteratedFDeriv ℝ j Ψ y‖ ≤ B := by
    intro j
    have hc : Continuous (fun y => iteratedFDeriv ℝ j Ψ y) :=
      hΨ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) C0).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, fun y hy => hB y (mem_closedBall_zero_iff.mpr hy)⟩
  choose Bj hBj using hΨb
  choose Cl hCl using hyp
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = ∑ j ∈ Finset.range (m + 1), |Bj j| := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = 1 + ∑ l ∈ Finset.range (m + 1), |Cl l| := ⟨_, rfl⟩
  have hBs0 : 0 ≤ Bs := by
    rw [hBs]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hCs1 : 1 ≤ Cs := by
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (m + 1)) => abs_nonneg (Cl l))
    rw [hCs]
    linarith
  have hBj' : ∀ j ≤ m, Bj j ≤ Bs := by
    intro j hj
    rw [hBs]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Bj j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega)))
  have hCl' : ∀ l ≤ m, Cl l ≤ Cs := by
    intro l hl
    have := (le_abs_self (Cl l)).trans (Finset.single_le_sum (f := fun l => |Cl l|) (fun l _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega : l < m + 1)))
    rw [hCs]
    linarith
  refine ⟨(m + 1).factorial * Bs * Cs ^ m, ?_⟩
  intro u v hu hv huv g hg
  have hgG := hKG hg
  have hg1 : 1 ≤ gN g := gN_ge_one hgG
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = gN g ^ Bg := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Real.one_le_rpow hg1 hBg
  have hpow : ∀ l : ℕ, gN g ^ (Bg * l) = a ^ l := by
    intro l
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast, ha]
  have hsub : ∀ s : List (Bool × Mat k r), s.Sublist (wL u ++ wR v) → ‖Dw s F g‖ ≤ Cs * a ^ s.length := by
    intro s hs
    unfold wL wR at hs
    obtain ⟨r1, r2, rfl, h1, h2⟩ := List.sublist_append_iff.mp hs
    obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.mp h1
    obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.mp h2
    have hl : u'.length + v'.length ≤ m := by
      have := hu'.length_le
      have := hv'.length_le
      omega
    have e : Dw (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)) F g = dLR u' v' F g := by
      rw [dLR_eq]
      rfl
    rw [e]
    have hb := hCl (u'.length + v'.length) u' v' (fun X hX => hu X (hu'.subset hX))
      (fun X hX => hv X (hv'.subset hX)) le_rfl g hg
    rw [hpow] at hb
    have hlen : (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)).length = u'.length + v'.length := by simp
    rw [hlen]
    calc ‖dLR u' v' F g‖ ≤ Cl (u'.length + v'.length) * a ^ (u'.length + v'.length) := hb
      _ ≤ Cs * a ^ (u'.length + v'.length) :=
        mul_le_mul_of_nonneg_right (hCl' _ hl) (pow_nonneg (by linarith) _)
  rw [dLR_eq]
  have hw : ∀ y ∈ wL u ++ wR v, inLie k r y.2 := by
    intro y hy
    simp only [wL, wR, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  obtain ⟨ts, hlen, hts, hval⟩ := expand hΨ hU hF (wL u ++ wR v) hw
  rw [hval g (hKU hg) hgG]
  have hL : (wL u ++ wR v).length ≤ m := by
    simp only [wL, wR, List.length_append, List.length_map]
    omega
  have hX : 0 ≤ Bs * Cs ^ m * gN g ^ (Bg * m) :=
    mul_nonneg (mul_nonneg hBs0 (pow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)
  have hterm : ∀ t ∈ ts, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m) := by
    intro t ht
    obtain ⟨hj, hsum, hsl⟩ := hts t ht
    rw [hpow]
    unfold tval
    calc ‖iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)‖
        ≤ ‖iteratedFDeriv ℝ t.j Ψ (F g)‖ * ∏ i, ‖Dw (t.ws i) F g‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ Bs * ∏ i, (Cs * a ^ (t.ws i).length) := by
          apply mul_le_mul ((hBj t.j (F g) (hFb g hg)).trans (hBj' _ (by omega)))
            (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hsub _ (hsl i)))
            (Finset.prod_nonneg fun i _ => norm_nonneg _) hBs0
      _ = Bs * (Cs ^ t.j * a ^ (wL u ++ wR v).length) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ Bs * (Cs ^ m * a ^ m) := by
          apply mul_le_mul_of_nonneg_left _ hBs0
          exact mul_le_mul (pow_le_pow_right₀ hCs1 (by omega)) (pow_le_pow_right₀ ha1 hL)
            (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
      _ = Bs * Cs ^ m * a ^ m := by ring
  have key : ∀ l : List (Tm k r), (∀ t ∈ l, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m)) →
      ‖(l.map fun t => tval Ψ F t g).sum‖ ≤ l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := by
    intro l
    induction l with
    | nil =>
      intro _
      simp
    | cons t l ih =>
      intro hl
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      calc _ ≤ ‖tval Ψ F t g‖ + ‖(l.map fun t => tval Ψ F t g).sum‖ := norm_add_le _ _
        _ ≤ (Bs * Cs ^ m * gN g ^ (Bg * m)) + l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) :=
          add_le_add (hl t (by simp)) (ih fun t' ht' => hl t' (by simp [ht']))
        _ = _ := by ring
  have hfac : (ts.length : ℝ) ≤ ((m + 1).factorial : ℝ) := by
    exact_mod_cast hlen.trans (Nat.factorial_le (by omega))
  calc ‖(ts.map fun t => tval Ψ F t g).sum‖ ≤ ts.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := key ts hterm
    _ ≤ ((m + 1).factorial : ℝ) * (Bs * Cs ^ m * gN g ^ (Bg * m)) := mul_le_mul_of_nonneg_right hfac hX
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
