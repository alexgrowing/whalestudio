import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

universe v u

namespace CrystallineSemistableComparison.HT

open Pb

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem sq_surj (a b : IdF A) {T : C} (x : sqM a b T) : ∃ (y : A.obj T) (hy : y ∈ a.S T), sqMk a b y hy = x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

theorem sq_eq (a b : IdF A) {T : C} {x y : A.obj T} (hx : x ∈ a.S T) (hy : y ∈ a.S T) :
    sqMk a b x hx = sqMk a b y hy ↔ x - y ∈ b.S T := Subtype.ext_iff.trans Ideal.Quotient.eq

def out (a b : IdF A) {T : C} (x : sqM a b T) : A.obj T := (sq_surj a b x).choose

theorem out_mem (a b : IdF A) {T : C} (x : sqM a b T) : out a b x ∈ a.S T := (sq_surj a b x).choose_spec.choose

theorem mk_out (a b : IdF A) {T : C} (x : sqM a b T) : sqMk a b (out a b x) (out_mem a b x) = x :=
  (sq_surj a b x).choose_spec.choose_spec

structure MulOk (a b a' b' a'' b'' : IdF A) : Prop where
  aa : ∀ (T : C) {x y : A.obj T}, x ∈ a.S T → y ∈ a'.S T → x * y ∈ a''.S T
  ab : ∀ (T : C) {x y : A.obj T}, x ∈ a.S T → y ∈ b'.S T → x * y ∈ b''.S T
  ba : ∀ (T : C) {x y : A.obj T}, x ∈ b.S T → y ∈ a'.S T → x * y ∈ b''.S T

variable {a b a' b' a'' b'' : IdF A} (h : MulOk a b a' b' a'' b'')

def MulOk.mul {T : C} (x : sqM a b T) (y : sqM a' b' T) : sqM a'' b'' T :=
  sqMk a'' b'' (out a b x * out a' b' y) (h.aa T (out_mem a b x) (out_mem a' b' y))

theorem MulOk.mul_mk {T : C} (x y : A.obj T) (hx : x ∈ a.S T) (hy : y ∈ a'.S T) :
    h.mul (sqMk a b x hx) (sqMk a' b' y hy) = sqMk a'' b'' (x * y) (h.aa T hx hy) := by
  refine (sq_eq _ _ _ _).2 ?_
  have h1 := (sq_eq _ _ _ _).1 (mk_out a b (sqMk a b x hx))
  have h2 := (sq_eq _ _ _ _).1 (mk_out a' b' (sqMk a' b' y hy))
  have := add_mem (h.ba T h1 (out_mem a' b' (sqMk a' b' y hy))) (h.ab T hx h2)
  convert this using 1
  ring

theorem mk_add (a b : IdF A) {T : C} {x y : A.obj T} (hx : x ∈ a.S T) (hy : y ∈ a.S T) :
    sqMk a b x hx + sqMk a b y hy = sqMk a b (x + y) (add_mem hx hy) := rfl

theorem mk_smul (a b : IdF A) {T : C} (r : R) {x : A.obj T} (hx : x ∈ a.S T) :
    r • sqMk a b x hx = sqMk a b (r • x) (Submodule.smul_of_tower_mem _ r hx) := rfl

theorem map_mk (a b : IdF A) {T T' : C} (φ : T ⟶ T') {x : A.obj T} (hx : x ∈ a.S T) :
    sqMap a b φ (sqMk a b x hx) = sqMk a b ((A.map φ).hom x) (a.map_mem φ hx) := rfl

def MulOk.pair : CH.Pairing (sq a b) (sq a' b') (sq a'' b'') where
  μ T := LinearMap.mk₂ R (fun (x : sqM a b T) (y : sqM a' b' T) => h.mul x y)
    (fun x x' y => by
      obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x; obtain ⟨x', hx', rfl⟩ := sq_surj _ _ x'; obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      rw [mk_add, h.mul_mk, h.mul_mk, h.mul_mk, mk_add]; exact (sq_eq _ _ _ _).2 (by rw [add_mul, sub_self]; exact zero_mem _))
    (fun r x y => by
      obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x; obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      rw [mk_smul, h.mul_mk, h.mul_mk, mk_smul]; exact (sq_eq _ _ _ _).2 (by rw [smul_mul_assoc, sub_self]; exact zero_mem _))
    (fun x y y' => by
      obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x; obtain ⟨y', hy', rfl⟩ := sq_surj _ _ y'; obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      rw [mk_add, h.mul_mk, h.mul_mk, h.mul_mk, mk_add]; exact (sq_eq _ _ _ _).2 (by rw [mul_add, sub_self]; exact zero_mem _))
    (fun r x y => by
      obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x; obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      rw [mk_smul, h.mul_mk, h.mul_mk, mk_smul]; exact (sq_eq _ _ _ _).2 (by rw [mul_smul_comm, sub_self]; exact zero_mem _))
  nat {T T'} φ (x : sqM a b T) (y : sqM a' b' T) := by
    obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x; obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    change h.mul (sqMap a b φ _) (sqMap a' b' φ _) = sqMap a'' b'' φ (h.mul _ _)
    simp only [map_mk, h.mul_mk, map_mul]

end Gen

theorem dividedPowerFiltration_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r s : ℕ) {x y : B} (hx : x ∈ pdP δ r)
    (hy : y ∈ pdP δ s) : x * y ∈ pdP δ (r + s) := by
  have : pdP δ r * pdP δ s ≤ pdP δ (r + s) := by
    unfold pdP
    rw [Ideal.span_mul_span']
    refine Ideal.span_mono ?_
    rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
    refine ⟨l ++ l', fun q hq => (List.mem_append.1 hq).elim (hl q) (hl' q), ?_, ?_⟩
    · simp only [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.prod_append]
  exact this (Ideal.mul_mem_mul hx hy)

section Thick
variable {b : Base} (L : b.Fun)

theorem grOk {a a' c : ℕ} (h : a + a' = c) :
    MulOk (thFil L a) (thFil L ((a : ℤ) + 1)) (thFil L a') (thFil L ((a' : ℤ) + 1)) (thFil L c) (thFil L ((c : ℤ) + 1)) where
  aa T _ _ hx hy := h ▸ dividedPowerFiltration_mul T.δ a a' hx hy
  ab T _ _ hx hy := h ▸ dividedPowerFiltration_mul T.δ a (a' + 1) hx hy
  ba T x y hx hy := by
    have := dividedPowerFiltration_mul T.δ (a + 1) a' hx hy
    rw [show a + 1 + a' = c + 1 by omega] at this
    exact this

abbrev grT (a : ℕ) : Thick L ⥤ ModuleCat.{0} b.R := sq (thFil L (a : ℤ)) (thFil L ((a : ℤ) + 1))

end Thick

section Hodge
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Hdg (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) : Type 1 := CH.H (grT (smFun X q) a) n

variable (q : X ⟶ Spec (CommRingCat.of K))

instance (a n : ℕ) : AddCommGroup (Hdg q a n) := inferInstanceAs (AddCommGroup (CH.H (grT (smFun X q) a) n))
instance (a n : ℕ) : Module K (Hdg q a n) := inferInstanceAs (Module (infBase K).R (CH.H (grT (smFun X q) a) n))

def cupH {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) (x : Hdg q a i) (y : Hdg q a' j) : Hdg q c n :=
  (grOk (smFun X q) ha).pair.cup h x y

def oneH : Hdg q 0 0 :=
  (toSq (thFil (smFun X q) (0 : ℕ)) (thFil (smFun X q) (((0 : ℕ) : ℤ) + 1)) fun T => T.pdPow_zero).pull 0 (CH.oneH (thA (smFun X q)))

def powH (x : Hdg q 1 2) : ∀ k : ℕ, Hdg q k (2 * k)
  | 0 => oneH q
  | k + 1 => cupH q rfl (by omega) (powH x k) x

variable {q}

def smS {p : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ p = q) :
    SMor (thP (smFun Y p)) (thP (smFun X q)) (RingHom.id K) where
  G := (smMor u hu).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

def pullH {p : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ p = q) (a n : ℕ) : Hdg p a n →ₗ[K] Hdg q a n :=
  ((smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
    (fun _ _ hx => hx) fun _ _ hx => hx).pull n

variable (q) in

def IsDlogFirstChernClass (D : E.LineData X) (x : Hdg q 1 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (g : C ⥤ Thick (smFun X q)), (∀ c, ∃ V ∈ 𝒱D D, InU V (g.obj c)) → ∀ Λ : CLiftK g D,
    Rep ((thFil (smFun X q) ((1 : ℕ) : ℤ)).res g) ((thFil (smFun X q) (((1 : ℕ) : ℤ) + 1)).res g)
      (fun σ : ComposableArrows C 2 => ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1 : (g.obj (σ.obj (Fin.last 2))).B))
      ((CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 x)

end Hodge

end CrystallineSemistableComparison.HT
