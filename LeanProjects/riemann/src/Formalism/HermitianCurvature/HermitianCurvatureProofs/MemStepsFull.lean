import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenBigCellSet

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma cd_eval (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => eval (vars g) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)
  next p q hp hq =>
    simpa using hp.add hq
  next p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases n with ⟨i, j⟩ | ⟨i, j⟩
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl]
      fun_prop
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]
      have h : ContDiff ℝ ∞ fun g : Mat k r => g i j := by fun_prop
      exact Complex.conjCLE.contDiff.comp h

lemma cd_dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ∞ (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, -, hq⟩ := dminPoly (k := k) z z' l
  have h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cd_gf (z z' : Fin (2 * r + k + 1) → ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  obtain ⟨q, -, hq⟩ := gfPoly (k := k) z z'
  have h : (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cda_invpow {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) {x : Mat k r} (a : ℕ) (h : a = 0 ∨ f x ≠ 0) :
    ContDiffAt ℝ ∞ (fun g => (f g)⁻¹ ^ a) x := by
  rcases h with rfl | h
  · simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  · exact (hf.contDiffAt.inv h).pow a

lemma cda_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma cda_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) {x : Mat k r} (hx : x ∈ V0 D L) : ContDiffAt ℝ ∞ (cvs D e.1) x := by
  obtain ⟨hab, -, -⟩ := he
  have hx0 : 0 < Gf k r D.z D.z' x := hx.1
  have hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0 := fun l hl => Set.mem_iInter₂.1 hx.2 l hl
  have hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG := hx0
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))
    linarith
  have hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0 := fun l hl => by
    rcases hab l hl with hl | rfl
    · exact hxL l hl
    · exact hlast
  have hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0 := fun l => by
    by_cases h : e.1.a l = 0
    · exact Or.inl h
    · exact Or.inr (hnz l (Or.inl h))
  have hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0 := fun l => by
    by_cases h : e.1.b l = 0
    · exact Or.inl h
    · right
      simpa using hnz l (Or.inr h)
  show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x
  refine (cd_eval _).contDiffAt.mul ?_
  refine (cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l *
      (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_
  · exact (cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul
      (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))
  · exact cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))

lemma ckOn_mul {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hA g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hfe'⟩ := hB g₀ hg₀
  refine ⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩
  · exact (hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)
  · intro g hg hgG
    simp only [hfe g hg.1 hgG, hfe' g hg.2 hgG]

lemma ckOn_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) → CkOn ⊤ (GPos D) (C6.Epart fib es) := by
  intro es
  induction es with
  | nil =>
    intro _ g₀ _
    refine ⟨univ, fun _ => 1, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩
    intro g _ _
    simp [C6.Epart]
  | cons e es ih =>
    intro hes
    have h1 := ckOn_Rw_top (hfib e.1) (hes e (by simp))
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    exact ckOn_mul h1 h2

lemma ckOn_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) : CkOn ⊤ (C6.domL D L) (cv D fib e.1) := by
  intro g₀ hg₀
  have hgpos : g₀ ∈ GPos D := domL_gpos hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos
  have hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L) :=
    (isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)
  refine ⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩
  · exact (hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)
  · intro g hg hgG
    simp only [cv, hfe g hg.1 hgG]

def mulCT {nf : ℕ} (t₁ t₂ : CT k r nf) : CT k r nf :=
  ⟨t₁.q * t₂.q, t₁.a + t₂.a, t₁.b + t₂.b, t₁.c + t₂.c, t₁.es ++ t₂.es⟩

lemma cv_mul (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t₁ t₂ : CT k r nf)
    (g : Mat k r) : cv D fib (mulCT t₁ t₂) g = cv D fib t₁ g * cv D fib t₂ g := by
  simp only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply,
    pow_add, Finset.prod_mul_distrib]
  rw [smul_mul_smul_comm]
  congr 1
  ring

lemma good_mul {nf : ℕ} {L : Finset (Fin (r + 2))} {e₁ e : CT k r nf × List (Mat k r)} (h₁ : Good L e₁)
    (h : Good L e) : Good L (mulCT e₁.1 e.1, e.2) := by
  unfold Good at h₁ h ⊢
  obtain ⟨ha1, hs1, -⟩ := h₁
  obtain ⟨ha, hs, hw⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_, hw⟩
  · by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
    · exact ha1 l h1
    · apply ha l
      push_neg at h1
      simpa [mulCT, h1.1, h1.2] using hl
  · simp only [mulCT, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs1 x hx
    · exact hs x hx

def fo {nf : ℕ} (es : List (Fin nf × List (Mat k r))) : ℕ := (es.map fun e => e.2.length).sum

lemma fo_set {nf : ℕ} (X : Mat k r) :
    ∀ (es : List (Fin nf × List (Mat k r))) (i : Fin es.length),
      fo (es.set i ((es.get i).1, X :: (es.get i).2)) = fo es + 1 := by
  intro es
  induction es with
  | nil => intro i; exact i.elim0
  | cons e es ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · simp [fo]
      omega
    · have hj' : j < es.length := by simpa using hj
      have := ih ⟨j, hj'⟩
      have e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) =
          e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2) := rfl
      show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) =
        fo (e :: es) + 1
      rw [e2]
      simp only [fo, List.map_cons, List.sum_cons] at this ⊢
      omega

lemma bound_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) :
    ∀ e' ∈ stepOne D X e, e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + 1 := by
  intro e' he'
  simp only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · rcases ht' with ht' | ht'
    · have hes := dscal_es D X e.1 t' ht'
      refine ⟨?_, by simp [hes]⟩
      simp only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'
      rcases ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl
      · exact (PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)
    · simp only [dfib, List.mem_ofFn] at ht'
      obtain ⟨i, rfl⟩ := ht'
      refine ⟨Nat.le_add_right _ _, ?_⟩
      simp only
      rw [fo_set]; omega
  · refine ⟨Nat.le_add_right _ _, by simp; omega⟩

lemma bound_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by
  intro w
  induction w with
  | nil =>
    intro Lf e' he'
    exact ⟨e', he', by simp, by simp⟩
  | cons X w ih =>
    intro Lf e' he'
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨e, he, hd, ho⟩ := ih Lf e'' he''
    obtain ⟨hd', ho'⟩ := bound_step D X e'' e' he'
    refine ⟨e, he, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      omega

lemma mem_steps_full (D : RealPlaceData k r Wp Wq) {nf : ℕ} (e : CT k r nf × List (Mat k r)) :
    ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w [e] := by
  intro w
  induction w with
  | nil => simp [steps]
  | cons X w ih =>
    simp only [steps, List.foldr_cons, step, List.mem_flatMap, List.cons_append]
    exact ⟨_, ih, by simp [stepOne]⟩

lemma steps_append (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L₁ L₂ : FS k r nf) :
    steps D w (L₁ ++ L₂) = steps D w L₁ ++ steps D w L₂ := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)
    rw [ih]
    simp [step, List.flatMap_append]

end Formalism.FourierDecayAlt.P.MinorPolynomials
