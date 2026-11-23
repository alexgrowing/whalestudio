import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

def KFin : Prop := ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  (a n : ℕ), FiniteDimensional K (Hdg q a n) ∧ (n < a → Subsingleton (Hdg q a n))

def DlogClassExistsUnique : Prop := ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X),
  sSup (Pb.𝒱D D) = ⊤ → ∃! c, IsDlogFirstChernClass q D c

def KTop : Prop := ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [ConnectedSpace X]
  (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X), Pb.IsTautologicalLine q D → ∀ c, IsDlogFirstChernClass q D c → powH q c d ≠ 0

structure KForm : Prop where
  bilin : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a a' c i j n : ℕ} (ha : a + a' = c)
    (h : i + j = n), ∃ b : Hdg q a i →ₗ[K] Hdg q a' j →ₗ[K] Hdg q c n, ∀ x y, b x y = cupH q ha h x y
  pull_id : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (u : X ⟶ X) (hu : u ≫ q = q), u = 𝟙 X →
    ∀ (a n : ℕ) (x : Hdg q a n), pullH u hu a n x = x
  pull_comp : ∀ {K : Type} [CommRing K] {X Y Z : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}
    {o : Z ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ p = q) (v : Y ⟶ Z) (hv : v ≫ o = p) (h : (u ≫ v) ≫ o = q) (a n : ℕ)
    (x : Hdg o a n), pullH (u ≫ v) h a n x = pullH u hu a n (pullH v hv a n x)
  pull_cup : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}
    (u : X ⟶ Y) (hu : u ≫ p = q) {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) (x : Hdg p a i) (y : Hdg p a' j),
    pullH u hu c n (cupH p ha h x y) = cupH q ha h (pullH u hu a i x) (pullH u hu a' j y)
  pull_one : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}
    (u : X ⟶ Y) (hu : u ≫ p = q), pullH u hu 0 0 (oneH p) = oneH q
  one_cup : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    cupH q (Nat.zero_add a) (Nat.zero_add n) (oneH q) x = x ∧ cupH q (Nat.add_zero a) (Nat.add_zero n) x (oneH q) = x
  assoc : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a b c ab bc s i j k ij jk n : ℕ}
    (h₁ : a + b = ab) (h₂ : ab + c = s) (h₃ : b + c = bc) (h₄ : a + bc = s) (e₁ : i + j = ij) (e₂ : ij + k = n) (e₃ : j + k = jk)
    (e₄ : i + jk = n) (x : Hdg q a i) (y : Hdg q b j) (z : Hdg q c k),
    cupH q h₂ e₂ (cupH q h₁ e₁ x y) z = cupH q h₄ e₄ x (cupH q h₃ e₃ y z)

end CrystallineSemistableComparison.HT
