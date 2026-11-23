import Development.EtaleCohomology.KummerTheory.LimitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LimLHPf

theorem cast_add' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by subst hn; subst hi; rfl

theorem cast_nsmul' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    (m • x).cast hn hi = m • x.cast hn hi := by subst hn; subst hi; rfl

theorem red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (x.cast hn hi) = (red Q q E n i x).cast hn hi := by subst hn; subst hi; rfl

theorem ext_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y y' : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold LateralTheory.KummerTheory.ext; rw [map_add, map_add, cast_add']

theorem ext_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (m : ℕ) (y : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold LateralTheory.KummerTheory.ext; rw [map_nsmul, map_nsmul, cast_nsmul']

theorem red_ext (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold LateralTheory.KummerTheory.ext
  rw [red_cast, (hA Q q hq _).1, ← pull_red, ← pull_red]

theorem lh_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y y' : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (y + y') = lh q pX pY i r c M n y + lh q pX pY i r c M n y' := by
  unfold LateralTheory.KummerTheory.lh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_add _ _ _ _ _ _ _ _ _

theorem lh_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) (m : ℕ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (m • y) = m • lh q pX pY i r c M n y := by
  unfold LateralTheory.KummerTheory.lh
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_nsmul _ _ _ _ _ _ _ _ _

theorem red_lh (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht Q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht Q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    red Q q _ n i (lh Q pX pY i r c M n y) =
      lh q pX pY i r (fun a s => red Q q _ a i (c a s)) M n (fun a s => red Q q _ _ 0 (y a s)) := by
  unfold LateralTheory.KummerTheory.lh
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact red_ext hA Q q hq _ _ _ _ _ _ _

theorem lev_red (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) E n i (lev l x (k + 1)) = lev l x k := x.2 k

instance nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem dvd_succ (l k : ℕ) : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)

variable {l : ℕ} [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i)

def phiFun (hA : A11) (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k), fun k => by
    change red (l ^ (k + 1)) (l ^ k) _ n i (lh (l ^ (k + 1)) pX pY i r (fun a s => lev l (c a s) (k + 1)) M n
      (fun a s => lev l (y a s) (k + 1))) = _
    rw [red_lh hA _ _ (dvd_succ l k)]
    simp only [lev_red]⟩

def phi (hA : A11) : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
    Hl l (sch.obj (pullback pX pY)) n i where
  toFun := phiFun pX pY n i M r c hA
  map_add' y y' := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k + lev l (y' a s) k) =
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) +
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y' a s) k)
    rw [← lh_add]; rfl)
  map_smul' t y := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => (t • (show HtL l k _ _ _ from lev l (y a s) k))) =
      (t • (show HtL l k _ _ _ from lev l (phiFun pX pY n i M r c hA y) k))
    have h1 : (fun (a : Fin (M + 1)) (s : Fin (r a)) =>
        (t • (show HtL l k (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0 from lev l (y a s) k) : Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)) =
        (PadicInt.toZModPow k t).val • (fun (a : Fin (M + 1)) (s : Fin (r a)) => lev l (y a s) k) :=
      funext fun a => funext fun s => HtL.smul_eq l k k le_rfl _ _ _ t _
    rw [h1, lh_nsmul]
    exact (HtL.smul_eq l k k le_rfl _ _ _ t _).symm)

theorem phi_ker (hA : A11) (N : ℕ)
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
    (hy : phi pX pY n i M r c hA y = 0) : N • y = 0 := by
  funext a s
  apply Subtype.ext; funext k
  have h0 : lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) = 0 := by
    have := congrArg (fun z : Hl l (sch.obj (pullback pX pY)) n i => lev l z k) hy
    exact this
  have := congrFun (congrFun ((hiso k).1 _ h0) a) s
  exact this

theorem phi_coker (hA : A11) (N : ℕ)
    (hfin : ∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0))
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (b : Hl l (sch.obj (pullback pX pY)) n i) : ∃ y, phi pX pY n i M r c hA y = N • b := by
  let D : ℕ → Type 1 := fun k => ∀ a : Fin (M + 1), Fin (r a) → Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0
  let Sl : ℕ → Type 1 := fun k => {z : D k // lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n z = N • lev l b k}
  let f : ∀ k, Sl (k + 1) ⟶ Sl k := fun k => TypeCat.ofHom fun (z : Sl (k + 1)) => (⟨fun a s => red (l ^ (k + 1)) (l ^ k) _ _ 0 (z.1 a s), by
    have h := congrArg (red (l ^ (k + 1)) (l ^ k) _ n i) z.2
    rw [red_lh hA _ _ (dvd_succ l k), map_nsmul, lev_red] at h
    simp only [lev_red] at h
    exact h⟩ : Sl k)
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence f
  have : ∀ j, Finite (F.obj j) := fun j => by
    have := hfin (unop j)
    change Finite (Sl (unop j))
    have : ∀ (a : Fin (M + 1)), Finite (Fin (r a) → Ht (l ^ unop j) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :=
      fun a => by have := hfin (unop j) (n - ((a : ℕ) : ℤ)); infer_instance
    have : Finite (D (unop j)) := Pi.finite
    exact Subtype.finite
  have : ∀ j, Nonempty (F.obj j) := fun j => by
    obtain ⟨z, hz⟩ := (hiso (unop j)).2 (lev l b (unop j))
    exact ⟨(⟨z, hz⟩ : Sl (unop j))⟩
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hstep : ∀ k a s, red (l ^ (k + 1)) (l ^ k) _ _ 0 (((sec (op (k + 1)) : Sl (k + 1)).1) a s) =
      ((sec (op k) : Sl k).1) a s := by
    intro k a s
    have h := hsec (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg (fun z : Sl k => z.1 a s) h
  refine ⟨fun a s => ⟨fun k => ((sec (op k) : Sl k).1) a s, fun k => hstep k a s⟩, ?_⟩
  apply Subtype.ext; funext k
  exact (sec (op k) : Sl k).2

theorem LimLH_of : LimLH := by
  intro hA l _ X Y S pX pY n i M N r c hfin hiso
  exact ⟨phi pX pY n i M r c hA, fun y k => rfl,
    fun y hy => phi_ker pX pY n i M r c hA N hiso y hy, fun b => phi_coker pX pY n i M r c hA N hfin hiso b⟩

end LateralTheory.KummerTheory.LimLHPf
