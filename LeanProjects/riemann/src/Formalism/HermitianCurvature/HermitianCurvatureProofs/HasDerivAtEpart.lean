import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtCvs

open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma Rw_cons' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Mat k r) (w : List (Mat k r))
    (f : Mat k r → E) : Rw (X :: w) f = Dx (false, X) (Rw w f) := by
  rfl

lemma ckOn_Rw_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)} {f : Mat k r → E}
    (hf : CkOn ⊤ UU f) {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) : CkOn ⊤ UU (Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    rw [Rw_cons']
    have h := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    exact CkOn_Dx (x := (false, X)) (hw X (by simp)) (by simpa using h)

theorem hasDerivAt_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) →
      HasDerivAt (fun s => C6.Epart fib es (crv (false, X) g s))
        (∑ i : Fin es.length, C6.Epart fib (es.set i ((es.get i).1, X :: (es.get i).2)) g) 0 := by
  intro es
  induction es with
  | nil =>
    intro _
    simp only [C6.Epart, List.map_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  | cons e es ih =>
    intro hes
    have h1 : HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s)) (Rw (X :: e.2) (fib e.1) g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX
        (sCkOn_mono le_top (ckOn_Rw_top (hfib e.1) (hes e (by simp)))) hg hg.1
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.mul h2
    show HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s) * C6.Epart fib es (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    have key : ∀ f : Fin (e :: es).length → C6.EndH Wp Wq,
        ∑ i, f i = f ⟨0, by simp⟩ + ∑ i : Fin es.length, f i.succ := fun f => Fin.sum_univ_succ f
    rw [key, crv_zero]
    simp [C6.Epart, Finset.mul_sum]

lemma list_sum_apply {α : Type*} (L : List α) (f : α → C6.EndH Wp Wq) (x : Wq →L[ℂ] Wp) :
    (L.map f).sum x = (L.map fun t => f t x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma list_sum_smul {α : Type*} (L : List α) (f : α → ℂ) (E : C6.EndH Wp Wq) :
    (L.map fun t => f t • E).sum = (L.map f).sum • E := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, add_smul]

lemma dscal_es (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) :
    ∀ t' ∈ dscal D X t, t'.es = t.es := by
  intro t' ht'
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h <;> (try split_ifs) <;> rfl

theorem hasDerivAt_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D)
    (t : CT k r nf) (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) (hes : ∀ e ∈ t.es, ∀ Y ∈ e.2, inLie k r Y) :
    HasDerivAt (fun s => cv D fib t (crv (false, X) g s)) (((dco D X t).map fun t' => cv D fib t' g).sum) 0 := by
  have h1 := hasDerivAt_cvs D X g t hnz hG
  have h2 := hasDerivAt_epart D fib hfib hX hg t.es hes
  have h3 := h1.smul h2
  show HasDerivAt (fun s => cvs D t (crv (false, X) g s) • C6.Epart fib t.es (crv (false, X) g s)) _ 0
  refine h3.congr_deriv ?_
  rw [crv_zero, dco, List.map_append, List.sum_append, add_comm]
  symm
  congr 1
  · rw [← list_sum_smul]
    exact congrArg List.sum (List.map_congr_left (fun t' ht' => by simp only [cv, dscal_es D X t t' ht']))
  · simp only [dfib, List.map_ofFn, List.sum_ofFn, Function.comp_def, cv, cvs, Finset.smul_sum]

abbrev FS (k r nf : ℕ) : Type := List (CT k r nf × List (Mat k r))

def shape (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (L : FS k r nf) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (L.map fun e => cv D fib e.1 g (Rw e.2 F g)).sum

def stepOne (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) : FS k r nf :=
  (dco D X e.1).map (fun t' => (t', e.2)) ++ [(e.1, X :: e.2)]

def step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (L : FS k r nf) : FS k r nf := L.flatMap (stepOne D X)

def steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L : FS k r nf) : FS k r nf := w.foldr (step D) L

def Good {nf : ℕ} (L : Finset (Fin (r + 2))) (e : CT k r nf × List (Mat k r)) : Prop :=
  (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → l ∈ L ∨ l = Fin.last (r + 1)) ∧
  (∀ x ∈ e.1.es, ∀ Y ∈ x.2, inLie k r Y) ∧ (∀ Y ∈ e.2, inLie k r Y)

private lemma dscal_support_prop_of_support_prop (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf)
    (P : Fin (r + 2) → Prop) (hP : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → P l) :
    ∀ t' ∈ dscal D X t, ∀ l, (t'.a l ≠ 0 ∨ t'.b l ≠ 0) → P l := by
  intro t' ht' l hl
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h
  · exact hP l hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inl hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inr hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl <;> exact hP l hl

lemma good_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {X : Mat k r} (hX : inLie k r X)
    {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    ∀ e' ∈ stepOne D X e, Good L e' ∧ e'.2.length ≤ e.2.length + 1 := by
  unfold Good at he ⊢
  obtain ⟨hab, hes, hw⟩ := he
  intro e' he'
  simp only [stepOne, List.mem_append, List.mem_map, List.mem_singleton] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · refine ⟨⟨?_, ?_, hw⟩, by simp⟩
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · exact dscal_support_prop_of_support_prop D X e.1 _ hab t' ht'
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        exact hab
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · rw [dscal_es D X e.1 t' ht']; exact hes
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        intro x hx Y hY
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hes x hx Y hY
        · rcases List.mem_cons.1 hY with rfl | hY
          · exact hX
          · exact hes _ (by simp) Y hY
  · refine ⟨⟨hab, hes, ?_⟩, by simp⟩
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact hX
    · exact hw Y hY

lemma good_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ (Lf : FS k r nf), (∀ e ∈ Lf, Good L e) →
      ∀ e' ∈ steps D w Lf, Good L e' ∧ ∃ e ∈ Lf, e'.2.length ≤ e.2.length + w.length := by
  intro w
  induction w with
  | nil =>
    intro _ Lf hLf e' he'
    exact ⟨hLf e' he', e', he', by simp⟩
  | cons X w ih =>
    intro hw Lf hLf e' he'
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨hg, e, he, hlen⟩ := ih hw' Lf hLf e'' he''
    obtain ⟨hg', hlen'⟩ := good_step D hX hg e' he'
    refine ⟨hg', e, he, ?_⟩
    simp only [List.length_cons]
    omega

end Formalism.FourierDecayAlt.P.MinorPolynomials
