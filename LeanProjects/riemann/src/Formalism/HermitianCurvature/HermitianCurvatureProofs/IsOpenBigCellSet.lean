import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtEpart

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def V0 (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (Mat k r) :=
  {x | 0 < Gf k r D.z D.z' x} ∩ ⋂ l ∈ L, {x | Dmin k r D.z D.z' x l ≠ 0}

lemma isOpen_big_cell_set (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : IsOpen (V0 D L) := by
  unfold V0
  refine (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter ?_
  refine isOpen_biInter_finset (fun l _ => ?_)
  exact isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const

lemma mem_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (g : Mat k r) :
    g ∈ C6.domL D L ↔ g ∈ GV k r ∧ g ∈ V0 D L := by
  simp only [C6.domL, V0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

lemma domL_gpos {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L) :
    g ∈ GPos D := by
  exact ⟨hg.1, hg.2.1⟩

lemma nz_of_domL {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L)
    {nf : ℕ} {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0) ∧
      (e.1.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) := by
  have hlast : Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG : 0 < Gf k r D.z D.z' g := hg.2.1
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' g ⟨r, by omega⟩))
    linarith
  obtain ⟨hab, -, -⟩ := he
  refine ⟨fun l hl => ?_, fun _ => ?_⟩
  · rcases hab l hl with hl | rfl
    · exact hg.2.2 l hl
    · exact hlast
  · exact_mod_cast hg.2.1.ne'

lemma shape_flatMap' (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (Lf : FS k r nf) (f : CT k r nf × List (Mat k r) → FS k r nf) (g : Mat k r) :
    shape D fib F (Lf.flatMap f) g = (Lf.map fun e => shape D fib F (f e) g).sum := by
  induction Lf with
  | nil => simp [shape]
  | cons e Lf ih =>
    simp only [shape] at ih ⊢
    simp [ih, List.sum_append]

private lemma ckOn_rw_of_ckOn_add_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)}
    {f : Mat k r → E} : ∀ (w : List (Mat k r)) (n : ℕ∞), (∀ X ∈ w, inLie k r X) →
      CkOn (n + w.length) UU f → CkOn n UU (Rw w f) := by
  intro w
  induction w with
  | nil => intro n _ hf; simpa [Rw] using hf
  | cons X w ih =>
    intro n hw hf
    rw [Rw_cons']
    refine CkOn_Dx (x := (false, X)) (hw X (by simp)) (ih (n + 1) (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) ?_)
    have e : n + 1 + (w.length : ℕ∞) = n + ((X :: w).length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [e]; exact hf

private lemma hasDerivAt_shape_crv_of_good (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    ∀ Lf : FS k r nf, (∀ e ∈ Lf, Good L e) → (∀ e ∈ Lf, e.2.length + 1 ≤ m) →
      HasDerivAt (fun s => shape D fib F Lf (crv (false, X) g s)) (shape D fib F (step D X Lf) g) 0 := by
  intro Lf
  induction Lf with
  | nil =>
    intro _ _
    simp only [shape, step, List.map_nil, List.sum_nil, List.flatMap_nil]
    exact hasDerivAt_const _ _
  | cons e Lf ih =>
    intro hL hm
    have he : Good L e := hL e (by simp)
    have hgp := domL_gpos hg
    have hnz := nz_of_domL hg he
    have hcv := hasDerivAt_cv D fib hfib hX hgp e.1 hnz.1 hnz.2 he.2.1
    have hRw : CkOn 1 (GV k r) (Rw e.2 F) := by
      refine ckOn_rw_of_ckOn_add_length e.2 1 he.2.2 (sCkOn_mono ?_ hF)
      have := hm e (by simp)
      rw [add_comm]; exact_mod_cast this
    have hR : HasDerivAt (fun s => Rw e.2 F (crv (false, X) g s)) (Rw (X :: e.2) F g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX hRw hgp.1 hgp.1
    have hcv' := ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) hcv
    have h1 := hcv'.clm_apply hR
    have h2 := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.add h2
    show HasDerivAt (fun s => cv D fib e.1 (crv (false, X) g s) (Rw e.2 F (crv (false, X) g s)) +
      shape D fib F Lf (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    rw [crv_zero]
    have hs : shape D fib F (step D X (e :: Lf)) g =
        shape D fib F (stepOne D X e) g + shape D fib F (step D X Lf) g := by
      simp only [step, shape_flatMap', List.map_cons, List.sum_cons]
    rw [hs]
    congr 1
    simp only [shape, stepOne, List.map_append, List.map_map, List.sum_append, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← list_sum_apply, crv_zero]
    try rfl

theorem step_eq (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by
  have hd := hasDerivAt_shape_crv_of_good D fib hfib L hF hX hg Lf hL hm
  rw [← hd.deriv]
  exact Dx_eq (false, X) (shape D fib F Lf) g

theorem expand (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), (∀ X ∈ w, inLie k r X) → (∀ e ∈ Lf, Good L e) →
      (∀ e ∈ Lf, e.2.length + w.length ≤ m) → ∀ g ∈ C6.domL D L,
        Rw w (shape D fib F Lf) g = shape D fib F (steps D w Lf) g := by
  intro w
  induction w with
  | nil => intro Lf _ _ _ g _; rfl
  | cons X w ih =>
    intro Lf hw hL hm g hg
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hm' : ∀ e ∈ Lf, e.2.length + w.length ≤ m := fun e he => by
      have := hm e he; simp only [List.length_cons] at this; omega
    have hev : (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) =ᶠ[𝓝 0]
        (fun t => shape D fib F (steps D w Lf) (crv (false, X) g t)) := by
      have hV : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
      filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV] with t ht
      exact ih Lf hw' hL hm' _ ((mem_domL D L _).2 ⟨crv_mem (x := (false, X)) hX hg.1 t, ht⟩)
    have hgood := good_steps D w hw' Lf hL
    have hstep := step_eq D fib hfib L hF hX (Lf := steps D w Lf) (fun e he => (hgood e he).1)
      (fun e he => by
        obtain ⟨-, e0, he0, hle⟩ := hgood e he
        have := hm e0 he0
        simp only [List.length_cons] at this
        omega) hg
    calc Rw (X :: w) (shape D fib F Lf) g
        = deriv (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) 0 := by
          rw [Rw_cons']; exact Dx_eq (false, X) _ g
      _ = deriv (fun t : ℝ => shape D fib F (steps D w Lf) (crv (false, X) g t)) 0 := hev.deriv_eq
      _ = RdV X (shape D fib F (steps D w Lf)) g := (Dx_eq (false, X) _ g).symm
      _ = shape D fib F (steps D (X :: w) Lf) g := hstep

end Formalism.FourierDecayAlt.P.MinorPolynomials
