import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type}

abbrev BV (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) : Type :=
  ∀ _ : PLift (∀ j ∈ s, b ≤ e j), M b

def bRes (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s t : Finset κ} (h : s ⊆ t) :
    BV e M b s →ₗ[R] BV e M b t where
  toFun x ht := x ⟨fun j hj ↦ ht.down j (h hj)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cubeB (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (BV e M b s)) (fun h ↦ bRes e M b h) (fun _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl)

theorem cubeB_bijective [DecidableEq κ] (e : κ → P) (M : P → ModuleCat.{0} R) {b : P} {i : κ} (hi : e i = b)
    (s : Finset κ) (_his : i ∉ s) :
    Function.Bijective (Cube.res (cubeB e M b) (Finset.subset_insert i s)) := by
  have key : ∀ hs : PLift (∀ j ∈ s, b ≤ e j), ∀ j ∈ insert i s, b ≤ e j := fun hs j hj ↦ by
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hi.ge
    · exact hs.down j hj
  constructor
  · intro x y h
    exact funext fun hs ↦ congrFun h ⟨key hs⟩
  · intro y
    exact ⟨fun hs ↦ (show BV e M b (insert i s) from y) ⟨key hs⟩, rfl⟩

abbrev AV (e : κ → P) (M : P → ModuleCat.{0} R) (s : Finset κ) : Type :=
  ∀ hs : PLift s.Nonempty, ∀ b : {b : P // b ≤ s.inf' hs.down e}, M b.1

def prj (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) :
    (cubeOf e (coind M)).obj s →ₗ[R] (cubeB e M b).obj s where
  toFun x := fun h ↦ if hs : s.Nonempty then
    (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ else 0
  map_add' x y := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; exact (add_zero _).symm
  map_smul' r x := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; show (0 : M b) = r • (0 : M b); exact (smul_zero r).symm

theorem prj_apply (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) (h : PLift (∀ j ∈ s, b ≤ e j)) :
    (show BV e M b s from prj e M b s x) h =
      (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ :=
  dif_pos hs

theorem prj_empty (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : ¬ s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) : prj e M b s x = 0 :=
  funext fun _ ↦ dif_neg hs

def prjHom (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : cubeOf e (coind M) ⟶ cubeB e M b :=
  Cube.homMk (prj e M b) fun {s t} h x ↦ by
    by_cases hs : s.Nonempty
    · refine funext fun ht ↦ ?_
      have hs' : t.Nonempty := hs.mono h
      refine (prj_apply e M b hs' _ ht).trans ?_
      refine Eq.trans ?_ (prj_apply e M b hs x ⟨fun j hj ↦ ht.down j (h hj)⟩).symm
      have := cubeRes_apply e (coind M) h x hs ⟨hs'⟩
      exact congrFun this _
    · rw [prj_empty e M b hs, map_zero]
      by_cases ht : t.Nonempty
      · refine funext fun hh ↦ ?_
        refine (prj_apply e M b ht _ hh).trans ?_
        have := cubeRes_empty e (coind M) h x hs ⟨ht⟩
        exact congrFun this _
      · exact prj_empty e M b ht _

theorem term_ext (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (u v : Cube.Term (cubeOf e (coind M)) (q + 1))
    (h : ∀ b, Cube.termMap (prjHom e M b) (q + 1) u = Cube.termMap (prjHom e M b) (q + 1) v) :
    u = v := by
  funext s
  refine funext fun hs ↦ funext fun b ↦ ?_
  have hle : ∀ j ∈ s.1, b.1 ≤ e j := fun j hj ↦ b.2.trans (Finset.inf'_le e hj)
  have h1 := congrFun (congrFun (h b.1) s) ⟨hle⟩
  exact (prj_apply e M b.1 hs.down (u s) ⟨hle⟩).symm.trans (h1.trans (prj_apply e M b.1 hs.down (v s) ⟨hle⟩))

def asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ} (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) :
    Cube.Term (cubeOf e (coind M)) (q + 1) :=
  fun s ↦ (show AV e M s.1 from fun _ b ↦
    (show BV e M b.1 s.1 from y b.1 s) ⟨fun _ hj ↦ b.2.trans (Finset.inf'_le e hj)⟩)

theorem termMap_asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) (b : P) :
    Cube.termMap (prjHom e M b) (q + 1) (asm e M y) = y b := by
  funext s
  refine funext fun h ↦ ?_
  have hs : s.1.Nonempty := Finset.card_pos.1 (by have := s.2; omega)
  exact prj_apply e M b hs (asm e M y s) h

variable [LinearOrder κ]

theorem exact_d (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (p : ℕ) :
    Function.Exact (Cube.d (cubeOf e (coind M)) (p + 1)) (Cube.d (cubeOf e (coind M)) (p + 2)) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ _ y⟩
  have hb : ∀ b, ∃ y : Cube.Term (cubeB e M b) (p + 1),
      Cube.d (cubeB e M b) (p + 1) y = Cube.termMap (prjHom e M b) (p + 2) x := by
    intro b
    obtain ⟨i, hi⟩ := he b
    refine (Cube.exact_d_of_bijective (cubeB e M b) i (cubeB_bijective e M hi) (p + 1) _).1 ?_
    rw [← Cube.termMap_d, hx, map_zero]
  choose y hy using hb
  refine ⟨asm e M y, term_ext e M _ _ fun b ↦ ?_⟩
  rw [Cube.termMap_d, termMap_asm, hy]

theorem isZero_homology (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (n : ℕ) :
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff (cubeOf e (coind M)) n).2 (exact_d e he M n))

example : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  fun e he M n ↦ isZero_homology e he M n

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc
