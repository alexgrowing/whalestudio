import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel

open scoped ContDiff ComplexConjugate

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def row (κ : ℂ) (pl : Bool) (Y : ℂ) (A B : ℂ → E) (s : Fin 2) : ℂ → E := fun τ =>
  if s = 0 then
    (if pl then (Y + κ) • A τ + τ • PBP.dz A τ - τ • B τ
     else (conj Y - κ) • A τ - conj τ • PBP.dzb A τ - conj τ • B τ)
  else (if pl then τ⁻¹ • A τ else (conj τ)⁻¹ • A τ)

section slots

variable {S : Type} [Fintype S] [DecidableEq S]

def rawA (κ : ℂ) (l : Wd.Letter ℂ S) (x : Wd.Ix S → ℂ → E) : Wd.Ix S → ℂ → E := fun e =>
  row κ l.plus l.pt (x (Function.update e l.intersection_update_fsHerm_neg_one 0)) (x (Function.update e l.intersection_update_fsHerm_neg_one 1)) (e l.intersection_update_fsHerm_neg_one)

def rawBT (κ : ℂ) : List (Wd.Letter ℂ S) → (Wd.Ix S → ℂ → E) → Wd.Ix S → ℂ → E
  | [], x => x
  | l :: w, x => rawA κ l (rawBT κ w x)

end slots

theorem dz_congr {f g : ℂ → E} {U : Set ℂ} (hU : IsOpen U) (h : ∀ τ ∈ U, f τ = g τ) {τ : ℂ} (hτ : τ ∈ U) :
    PBP.dz f τ = PBP.dz g τ := by
  have e : f =ᶠ[nhds τ] g := Filter.eventually_of_mem (hU.mem_nhds hτ) h
  unfold PBP.dz
  rw [e.fderiv_eq]

theorem dzb_congr {f g : ℂ → E} {U : Set ℂ} (hU : IsOpen U) (h : ∀ τ ∈ U, f τ = g τ) {τ : ℂ} (hτ : τ ∈ U) :
    PBP.dzb f τ = PBP.dzb g τ := by
  have e : f =ᶠ[nhds τ] g := Filter.eventually_of_mem (hU.mem_nhds hτ) h
  unfold PBP.dzb
  rw [e.fderiv_eq]

theorem row_congr (κ : ℂ) (pl : Bool) (Y : ℂ) {A B A' B' : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hA : ∀ τ ∈ U, A τ = A' τ) (hB : ∀ τ ∈ U, B τ = B' τ) (s : Fin 2) {τ : ℂ} (hτ : τ ∈ U) :
    row κ pl Y A B s τ = row κ pl Y A' B' s τ := by
  have h1 := dz_congr hU hA hτ
  have h2 := dzb_congr hU hA hτ
  simp only [row, hA τ hτ, hB τ hτ, h1, h2]

section positions2

variable {S : Type} [Fintype S] [DecidableEq S]

theorem rawBT_congr (κ : ℂ) (w : List (Wd.Letter ℂ S)) {x y : Wd.Ix S → ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (h : ∀ b, ∀ τ ∈ U, x b τ = y b τ) : ∀ e, ∀ τ ∈ U, rawBT κ w x e τ = rawBT κ w y e τ := by
  induction w with
  | nil => exact h
  | cons l w ih =>
    intro e τ hτ
    simp only [rawBT, rawA]
    exact row_congr κ l.plus l.pt hU (fun t ht => ih _ t ht) (fun t ht => ih _ t ht) (e l.intersection_update_fsHerm_neg_one) hτ

theorem word_action_mul (M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) :
    act1 (M * N) x = act1 M (act1 N x) := by
  funext a
  have hs : ∀ (s : Finset (Wd.Ix S)) (f : Wd.Ix S → Q.Pr (V1 E)), (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := by
    intro s f
    refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty]; rfl) (fun j t hj ih => ?_)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl
  have hm : ∀ p q : Q.Pr (V1 E), (p * q).1 = p.1 * q.1 := fun p q => rfl
  simp only [act1, Matrix.mul_apply, hs, hm, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  rw [Finset.sum_comm]

section pr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_add (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl
theorem pr_fst_neg (x : Q.Pr V) : (-x).1 = -x.1 := rfl
theorem pr_fst_zero : (0 : Q.Pr V).1 = 0 := rfl
theorem pr_fst_alg (Y : ℂ) : (algebraMap ℂ (Q.Pr V) Y).1 = algebraMap ℂ (Module.End ℂ V) Y := rfl
theorem pr_fst_star (x : Q.Pr V) : (star x).1 = x.2.unop := rfl
theorem pr_snd_add (x y : Q.Pr V) : (x + y).2.unop = x.2.unop + y.2.unop := rfl
theorem pr_snd_neg (x : Q.Pr V) : (-x).2.unop = -x.2.unop := rfl
theorem pr_snd_alg (Y : ℂ) : (algebraMap ℂ (Q.Pr V) Y).2.unop = algebraMap ℂ (Module.End ℂ V) (conj Y) := rfl
theorem mkPair_fst (X Xs : Module.End ℂ V) : (Q.mkP X Xs).1 = X := rfl
theorem snd_eq_of_mkPair_eq (X Xs : Module.End ℂ V) : (Q.mkP X Xs).2.unop = Xs := rfl

end pr

theorem pathSpace_add_apply (f g : V1 E) (τ : ℂ) : (f + g).1 τ = f.1 τ + g.1 τ := rfl
theorem pathSpace_neg_apply (f : V1 E) (τ : ℂ) : (-f).1 τ = -f.1 τ := rfl
theorem pathSpace_smul_apply (c : ℂ) (f : V1 E) (τ : ℂ) : (c • f).1 τ = c • f.1 τ := rfl
theorem pathSpace_zero_apply (τ : ℂ) : (0 : V1 E).1 τ = 0 := rfl
theorem opP_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    (opP κ f).1 τ = τ • PBP.dz f.1 τ + κ • f.1 τ := by
  simp [opP, off0, hτ]
theorem opPb_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    (opPb κ f).1 τ = conj τ • PBP.dzb f.1 τ + κ • f.1 τ := by
  simp [opPb, off0, hτ]
theorem opM_apply (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) (f : V1 E) (τ : ℂ) :
    (opM m hm f).1 τ = m τ • f.1 τ := rfl

theorem vlet_apply {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (σ : Wd.Site A) (l : Wd.Letter ℂ S)
    (e b : Wd.Ix S) :
    Wd.vlet σ l e b = if (∀ c, c ≠ l.intersection_update_fsHerm_neg_one → e c = b c) then
      (if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) (b l.intersection_update_fsHerm_neg_one) else 0 := by
  simp only [Wd.vlet, Wd.ins, Wd.lift0, Wd.io, Wd.eU, Matrix.sum_apply, Matrix.map_apply,
    Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  by_cases h : ∀ c, c ≠ l.intersection_update_fsHerm_neg_one → e c = b c
  · simp [h, ite_and]
  · simp [h]

private theorem sum_ite_eq_sum_update {R : Type} [Fintype R] [DecidableEq R] {β : Type} [AddCommMonoid β]
    (e : Wd.Ix R) (a : R) (g : Fin 2 → Wd.Ix R → β) :
    ∑ b : Wd.Ix R, (if (∀ c, c ≠ a → e c = b c) then g (b a) b else 0) =
      ∑ s : Fin 2, g s (Function.update e a s) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun s => Function.update e a s) (fun b => b a) ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro c hc
    rw [Function.update_of_ne hc]
  · intro b _
    exact Finset.mem_univ _
  · intro s _
    simp
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    funext c
    by_cases hc : c = a
    · subst hc
      simp
    · rw [Function.update_of_ne hc, hb c hc]
  · intro s _
    simp

theorem word_action_letter_apply (σ : Wd.Site (Q.Pr (V1 E))) (l : Wd.Letter ℂ S) (y : Wd.Ix S → V1 E) (e : Wd.Ix S) :
    act1 (Wd.vlet σ l) y e = ∑ s : Fin 2,
      ((if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) s).1
        (y (Function.update e l.intersection_update_fsHerm_neg_one s)) := by
  unfold act1
  refine (Finset.sum_congr rfl (fun b _ => ?_)).trans
    (sum_ite_eq_sum_update e l.intersection_update_fsHerm_neg_one (fun s b => ((if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) s).1 (y b)))
  rw [vlet_apply]
  split_ifs <;> rfl

theorem word_action_letter_site_apply (κ : ℂ) (l : Wd.Letter ℂ S) (y : Wd.Ix S → V1 E) (e : Wd.Ix S) {τ : ℂ} (hτ : τ ≠ 0) :
    (act1 (Wd.vlet (site1 κ) l) y e).1 τ = rawA κ l (fun b => (y b).1) e τ := by
  rw [word_action_letter_apply]
  obtain ⟨pl, a, Y⟩ := l
  simp only [rawA, row]
  generalize e a = s
  fin_cases s <;> cases pl <;>
    simp [Fin.sum_univ_two, pathSpace_add_apply, pathSpace_neg_apply, pathSpace_smul_apply, pathSpace_zero_apply, Wd.Ts, YangianSpanCharacter.T.Tm, site1,
      pr_fst_add, pr_fst_neg, pr_fst_zero, pr_fst_alg, pr_fst_star, pr_snd_add, pr_snd_neg,
      pr_snd_alg, mkPair_fst, snd_eq_of_mkPair_eq, opP_apply _ _ hτ, opPb_apply _ _ hτ, opM_apply] <;>
    first
    | rfl
    | (simp only [add_smul, sub_smul]; abel)

theorem oneBT_eq_raw (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    ∀ e, ∀ τ, τ ≠ 0 → (act1 (Wd.bT (site1 κ) w) x e).1 τ = rawBT κ w (fun b => (x b).1) e τ := by
  induction w with
  | nil =>
    intro e τ _
    have hx : act1 (Wd.bT (site1 κ) ([] : List (Wd.Letter ℂ S))) x e = x e := by
      rw [Wd.bT.eq_1]
      unfold act1
      rw [Finset.sum_eq_single e]
      · rw [Matrix.one_apply_eq]
        rfl
      · intro b _ hb
        rw [Matrix.one_apply_ne (Ne.symm hb)]
        rfl
      · intro h
        exact absurd (Finset.mem_univ e) h
    rw [hx]
    rfl
  | cons l w ih =>
    intro e τ hτ
    rw [Wd.bT.eq_2, word_action_mul, word_action_letter_site_apply κ l _ e hτ]
    simp only [rawBT, rawA]
    exact row_congr κ l.plus l.pt (U := {(0 : ℂ)}ᶜ) isOpen_compl_singleton
      (fun t ht => ih _ t ht) (fun t ht => ih _ t ht) (e l.intersection_update_fsHerm_neg_one) hτ

end positions2

section succ

theorem upd_succ_zero {n : ℕ} (e : Wd.Ix (Fin (n + 1))) (a : Fin n) (s : Fin 2) :
    Function.update e a.succ s 0 = e 0 :=
  Function.update_of_ne (Fin.succ_ne_zero a).symm _ _

theorem rawBT_map_succ (κ : ℂ) {n : ℕ} (L : List (Wd.Letter ℂ (Fin n))) (x : Wd.Ix (Fin (n + 1)) → ℂ → E) :
    rawBT κ (L.map fun m => (⟨m.plus, m.intersection_update_fsHerm_neg_one.succ, m.pt⟩ : Wd.Letter ℂ (Fin (n + 1)))) x =
      fun e => rawBT κ L (fun b => x (Fin.cons (e 0) b : Wd.Ix (Fin (n + 1)))) (Fin.tail e) := by
  induction L with
  | nil =>
    funext e
    simp only [List.map_nil, rawBT, Fin.cons_self_tail]
  | cons m L ih =>
    simp only [List.map_cons, rawBT]
    rw [ih]
    funext e
    simp only [rawA, upd_succ_zero, Fin.tail_update_succ]
    rfl

theorem positioned_cons (l : C.Letter) (w : List C.Letter) :
    D.positionted (l :: w) = (⟨l.1, 0, (l.2 : ℂ)⟩ : Wd.Letter ℂ (Fin (w.length + 1))) ::
      (D.positionted w).map fun m => (⟨m.plus, m.intersection_update_fsHerm_neg_one.succ, m.pt⟩ : Wd.Letter ℂ (Fin (w.length + 1))) := by
  unfold D.positionted
  rw [List.ofFn_succ, List.map_ofFn]
  rfl

theorem rawBT_indexed_cons (κ : ℂ) (l : C.Letter) (w : List C.Letter) (x : Wd.Ix (Fin (w.length + 1)) → ℂ → E)
    (e : Wd.Ix (Fin (w.length + 1))) :
    rawBT κ (D.positionted (l :: w)) x e =
      row κ l.1 (l.2 : ℂ) (rawBT κ (D.positionted w) (fun b => x (Fin.cons 0 b : Wd.Ix (Fin (w.length + 1)))) (Fin.tail e))
        (rawBT κ (D.positionted w) (fun b => x (Fin.cons 1 b : Wd.Ix (Fin (w.length + 1)))) (Fin.tail e)) (e 0) := by
  rw [positioned_cons]
  simp only [rawBT, rawA, rawBT_map_succ, Function.update_self, Fin.tail_update_zero]

end succ

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
