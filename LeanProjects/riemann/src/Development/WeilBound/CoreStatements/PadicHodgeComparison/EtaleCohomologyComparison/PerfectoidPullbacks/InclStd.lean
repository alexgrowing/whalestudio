import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

def stdI {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) : IdF (sP Q).A :=
  (match r with
    | none => IdF.bot _
    | some r => sFil Q r).sup (IdF.span _ c)

theorem incl_std {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) :
    (incl h).Le (stdI Q r c) (stdI Q' r c) := by
  intro T x hx
  cases r <;> exact hx

theorem incl_fil {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : ℤ) :
    (incl h).Le (sFil Q r) (sFil Q' r) := by
  intro T x hx
  exact hx

def FlatT {b : Base} {L : b.Fun} : ObjectProperty (Thick L) := fun T => T.i.Flat

def Used {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) : Prop :=
  (b.p = 0 ∧ ∃ l s, Q = TF l s) ∨ (b.p ≠ 0 ∧ (Q = ⊤ ∨ Q = FlatT))

structure TFBase {R : Type} [CommRing R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ) : Prop where
  nil : pdP γ s = ⊥
  tf : ∀ (r : ℕ) (x : R), (l : R) * x ∈ pdP γ r → x ∈ pdP γ r
  dv : ∀ n : ℕ, n ≠ 0 → ∃ (k : ℕ) (u : R), (n : R) * u = (l : R) ^ k

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev KS (s : ℕ) (𝒱 : Set X.Opens) : ObjectProperty (Thick (smFun X q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱

def resK (Q : ObjectProperty (Thick (smFun X q))) (j : ℕ) : HdR q j →ₗ[K] HO Q j := (CH.Mor.restrict (O (smFun X q)) Q.ι).pull j

def quoK (Q : ObjectProperty (Thick (smFun X q))) (r : ℤ) (j : ℕ) : HdR q j →ₗ[K] HQ Q 0 r j :=
  ((toSq (sFil Q 0) (sFil Q r) fun T => T.obj.pdPow_zero).pull j).comp (resK q Q j)

def cupK {i j n : ℕ} (h : i + j = n) (x : HdR q i) (y : HdR q j) : HdR q n := (CH.mulP (thA (smFun X q))).cup h x y

def oneK : HdR q 0 := CH.oneH (thA (smFun X q))

def powK (x : HdR q 2) : ∀ k : ℕ, HdR q (2 * k)
  | 0 => oneK q
  | k + 1 => cupK q (by omega) (powK x k) x

end K

end CrystallineSemistableComparison.Pb
