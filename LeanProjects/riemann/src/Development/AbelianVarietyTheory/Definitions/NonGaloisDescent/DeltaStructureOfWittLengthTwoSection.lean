import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism

namespace GlobalTheory.BSP

section W2

variable (l : ℕ) {A B : Type} [CommRing A] [CommRing B]

def cc (a b : A) : A := ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)

theorem map_cc (f : A →+* B) (a b : A) : f (cc l a b) = cc l (f a) (f b) := by simp [cc]

theorem l_mul_cc [hl : Fact l.Prime] (a b : A) : (l : A) * cc l a b = (a + b) ^ l - a ^ l - b ^ l := by
  rw [add_pow_prime_eq hl.out, cc, Finset.mul_sum]
  have : ∀ k ∈ Finset.Ioo 0 l, (l : A) * (((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)) =
      (l : A) * a * b * (a ^ (k - 1) * b ^ (l - k - 1) * ((l.choose k / l : ℕ) : A)) := fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, l - (i + 1) = j + 1 := ⟨l - (i + 1) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]; ring

@[ext] structure W2 (l : ℕ) (A : Type) where

  fst : A

  snd : A

namespace W2

variable {l}

instance : Zero (W2 l A) := ⟨⟨0, 0⟩⟩
instance : One (W2 l A) := ⟨⟨1, 0⟩⟩
instance : Add (W2 l A) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd - cc l x.fst y.fst⟩⟩
instance : Neg (W2 l A) := ⟨fun x => ⟨-x.fst, -x.snd + cc l (-x.fst) x.fst⟩⟩
instance : Mul (W2 l A) :=
  ⟨fun x y => ⟨x.fst * y.fst, x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd⟩⟩

def mapF (f : A →+* B) (x : W2 l A) : W2 l B := ⟨f x.fst, f x.snd⟩

theorem mapF_add (f : A →+* B) (x y : W2 l A) : mapF f (x + y) = mapF f x + mapF f y :=
  W2.ext (map_add f _ _) (by
    change f (x.snd + y.snd - cc l x.fst y.fst) = f x.snd + f y.snd - cc l (f x.fst) (f y.fst)
    rw [map_sub, map_add, map_cc])

theorem mapF_mul (f : A →+* B) (x y : W2 l A) : mapF f (x * y) = mapF f x * mapF f y :=
  W2.ext (map_mul f _ _) (by
    change f (x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd) =
      f x.fst ^ l * f y.snd + f y.fst ^ l * f x.snd + (l : B) * f x.snd * f y.snd
    simp)

def gh (x : W2 l A) : A := x.fst ^ l + (l : A) * x.snd

variable [hl : Fact l.Prime]

theorem gh_add (x y : W2 l A) : gh (x + y) = gh x + gh y := by
  change (x.fst + y.fst) ^ l + (l : A) * (x.snd + y.snd - cc l x.fst y.fst) = _
  simp only [gh]; linear_combination -l_mul_cc l x.fst y.fst

omit hl in

theorem gh_mul (x y : W2 l A) : gh (x * y) = gh x * gh y := by
  change (x.fst * y.fst) ^ l + (l : A) * (x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd) = _
  simp only [gh]; ring

theorem ext_gh {σ : Type} {x y : W2 l (MvPolynomial σ ℤ)} (h0 : x.fst = y.fst) (h1 : gh x = gh y) : x = y := by
  refine W2.ext h0 (mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : MvPolynomial σ ℤ) ≠ 0) ?_)
  simp only [gh, h0] at h1
  exact add_left_cancel h1

omit hl in

theorem exists_lift (x : W2 l A) :
    ∃ y : W2 l (MvPolynomial A ℤ), mapF (MvPolynomial.eval₂Hom (Int.castRingHom A) id) y = x :=
  ⟨⟨MvPolynomial.X x.fst, MvPolynomial.X x.snd⟩, W2.ext (by simp [mapF]) (by simp [mapF])⟩

instance : CommRing (W2 l A) := CommRing.ofMinimalAxioms
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_add]
    exact congrArg _ (ext_gh (add_assoc _ _ _) (by simp only [gh_add, add_assoc])))
  (fun x => W2.ext (zero_add _) (by
    change 0 + x.snd - cc l 0 x.fst = x.snd
    have : cc l 0 x.fst = 0 := Finset.sum_eq_zero fun k hk => by
      rw [zero_pow (Finset.mem_Ioo.1 hk).1.ne']; simp
    rw [this]; simp))
  (fun x => W2.ext (neg_add_cancel _) (by
    change -x.snd + cc l (-x.fst) x.fst + x.snd - cc l (-x.fst) x.fst = 0
    ring))
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_mul]
    exact congrArg _ (ext_gh (mul_assoc _ _ _) (by simp only [gh_mul, mul_assoc])))
  (fun x y => W2.ext (mul_comm _ _) (by
    change x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd =
      y.fst ^ l * x.snd + x.fst ^ l * y.snd + (l : A) * y.snd * x.snd
    ring))
  (fun x => W2.ext (one_mul _) (by
    change (1 : A) ^ l * x.snd + x.fst ^ l * 0 + (l : A) * 0 * x.snd = x.snd
    ring))
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_mul, ← mapF_add]
    exact congrArg _ (ext_gh (mul_add _ _ _) (by simp only [gh_mul, gh_add, mul_add])))

def map (f : A →+* B) : W2 l A →+* W2 l B where
  toFun := mapF f
  map_one' := W2.ext (map_one f) (map_zero f)
  map_zero' := W2.ext (map_zero f) (map_zero f)
  map_add' := mapF_add f
  map_mul' := mapF_mul f

def fstHom : W2 l A →+* A where
  toFun := fst
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def ghHom : W2 l A →+* A where
  toFun := gh
  map_one' := by change (1 : A) ^ l + (l : A) * 0 = 1; simp
  map_zero' := by change (0 : A) ^ l + (l : A) * 0 = 0; simp [hl.out.ne_zero]
  map_add' := gh_add
  map_mul' := gh_mul

end W2

variable {l} [hl : Fact l.Prime]

def deltaSectionToWittLengthTwo (D : Delta l A) : A →+* W2 l A where
  toFun a := ⟨a, D.δ a⟩
  map_one' := W2.ext rfl D.δ_one
  map_zero' := W2.ext rfl D.δ_zero
  map_add' a b := W2.ext rfl (D.δ_add a b)
  map_mul' a b := W2.ext rfl (D.δ_mul a b)

def deltaStructureOfWittLengthTwoSection (s : A →+* W2 l A) (h : ∀ a, (s a).fst = a) : Delta l A where
  δ a := (s a).snd
  δ_one := by rw [map_one]; rfl
  δ_mul a b := by rw [map_mul]; exact (congrArg₂ (fun x y => x ^ l * (s b).snd + y ^ l * (s a).snd +
    (l : A) * (s a).snd * (s b).snd) (h a) (h b))
  δ_add a b := by rw [map_add]; exact (congrArg₂ (fun x y => (s a).snd + (s b).snd - cc l x y) (h a) (h b))
  φ := W2.ghHom.comp s
  φ_eq a := congrArg (fun x => x ^ l + (l : A) * (s a).snd) (h a)

def IsδMap (D : Delta l A) (D' : Delta l B) (f : A →+* B) : Prop := ∀ a, f (D.δ a) = D'.δ (f a)

def δLocus (D : Delta l A) (D' : Delta l B) (f : A →+* B) : Subring A :=
  RingHom.eqLocus ((W2.map f).comp (deltaSectionToWittLengthTwo D)) ((deltaSectionToWittLengthTwo D').comp f)

theorem mem_δLocus {D : Delta l A} {D' : Delta l B} {f : A →+* B} {a : A} :
    a ∈ δLocus D D' f ↔ f (D.δ a) = D'.δ (f a) :=
  ⟨fun h => congrArg W2.snd h, fun h => W2.ext rfl h⟩

def polyDelta (D : Delta l A) : Delta l (MvPolynomial ℕ A) :=
  deltaStructureOfWittLengthTwoSection (MvPolynomial.eval₂Hom ((W2.map MvPolynomial.C).comp (deltaSectionToWittLengthTwo D))
                                      fun i => ⟨MvPolynomial.X i, MvPolynomial.X (i + 1)⟩)
    (RingHom.congr_fun (f := W2.fstHom.comp _) (g := RingHom.id _) (MvPolynomial.ringHom_ext
      (fun a => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]; rfl)
      (fun i => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']; rfl)))

theorem polyDelta_C (D : Delta l A) (a : A) :
    (polyDelta D).δ (MvPolynomial.C a) = MvPolynomial.C (D.δ a) :=
  congrArg W2.snd (MvPolynomial.eval₂Hom_C _ _ a)

theorem polyDelta_X (D : Delta l A) (i : ℕ) :
    (polyDelta D).δ (MvPolynomial.X i) = MvPolynomial.X (i + 1) :=
  congrArg W2.snd (MvPolynomial.eval₂Hom_X' _ _ i)

def envRel (D : Delta l A) (d p : A) (i : ℕ) : MvPolynomial ℕ A :=
  (polyDelta D).δ^[i + 1] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0)

end W2

structure IsCompl {L Q : Type} [CommRing L] [CommRing Q] (i : L →+* Q) (J : Ideal L) : Prop where
  complete : IsAdicComplete (J.map i) Q
  surj : ∀ (x : Q) (n : ℕ), ∃ a, x - i a ∈ (J ^ n).map i
  ker : ∀ (a : L) (n : ℕ), i a ∈ (J ^ n).map i → a ∈ J ^ n

theorem IsCompl.self {L : Type} [CommRing L] (J : Ideal L) [h : IsAdicComplete J L] : IsCompl (RingHom.id L) J :=
  ⟨by rwa [Ideal.map_id], fun x _ => ⟨x, by simp⟩, fun a n ha => by rwa [Ideal.map_id] at ha⟩

variable {l : ℕ}

abbrev JJ {R : Type} [CommRing R] (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

structure LocP {R : Type} [CommRing R] (B : Obj l R) (f d : B.A) where

  Q : Obj l R

  inl : Hom B Q
  unit : IsUnit (inl.f f)
  I_eq : Q.I = Ideal.span {inl.f d}
  univ : ∀ (C : Obj l R) (g : Hom B C), IsUnit (g.f f) → ∃! h : Hom Q C, h.comp inl = g
  surj : ∀ (x : Q.A) (n : ℕ), ∃ (k : ℕ) (b : B.A), inl.f f ^ k * x - inl.f b ∈ (JJ B ^ n).map inl.f
  ker : ∀ (b : B.A) (n : ℕ), inl.f b ∈ (JJ B ^ n).map inl.f → ∃ k : ℕ, f ^ k * b ∈ JJ B ^ n

def GenAway {R : Type} [CommRing R] (B : Obj l R) (f d : B.A) : Prop :=
  d ∈ B.I ∧ ∀ x ∈ B.I, ∃ k : ℕ, f ^ k * x ∈ Ideal.span {d}

structure EnvRing [Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A) where

  Q : Type
  [ring : CommRing Q]

  DQ : Delta l Q

  i : A →+* Q
  i_δ : IsδMap D DQ i

  w : Q
  rel : DQ.δ (i p + i d * w) = 0

  tb : TopBasis i J (Digits l)
  tb_b : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n
  lift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
    IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
    ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp i = f ∧ h w = v

attribute [instance] EnvRing.ring

end GlobalTheory.BSP
