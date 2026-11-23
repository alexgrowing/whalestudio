import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

structure PBData {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) where
  W' : Scheme.{0}
  c : W' ⟶ W
  [smc : Smooth c]
  [suc : Surjective c]
  g : ∀ {V : Scheme.{0}} (a b : V ⟶ W'), a ≫ c = b ≫ c → GL (Fin d) Γ(V, ⊤)
  g_nat : ∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ W') (h : a ≫ c = b ≫ c),
    g (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Matrix.GeneralLinearGroup.map s.appTop.hom (g a b h)
  g_coc : ∀ {V : Scheme.{0}} (a b k : V ⟶ W') (h : a ≫ c = b ≫ c) (h' : b ≫ c = k ≫ c), g b k h' * g a b h = g a k (h.trans h')
  T' : Scheme.{0}
  e : T' ⟶ T
  [sme : Smooth e]
  [sue : Surjective e]
  ρ : T' ⟶ W'
  comm : ρ ≫ c = e ≫ r
  v : ∀ {V : Scheme.{0}} (_ : V ⟶ T'), Um d Γ(V, ⊤)
  v_nat : ∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a : V ⟶ T'), (v (s ≫ a)).1 = s.appTop.hom ∘ (v a).1
  w : ∀ {V : Scheme.{0}} (a b : V ⟶ T'), a ≫ e = b ≫ e → (Γ(V, ⊤))ˣ
  gv : ∀ {V : Scheme.{0}} (a b : V ⟶ T') (h : a ≫ e = b ≫ e) (h' : (a ≫ ρ) ≫ c = (b ≫ ρ) ≫ c),
    (g _ _ h' : Matrix _ _ _).mulVec (v a).1 = (w a b h : Γ(V, ⊤)) • (v b).1
  inj : ∀ {V : Scheme.{0}} (a b : V ⟶ T') (h' : (a ≫ ρ) ≫ c = (b ≫ ρ) ≫ c) (u : (Γ(V, ⊤))ˣ),
    (g _ _ h' : Matrix _ _ _).mulVec (v a).1 = (u : Γ(V, ⊤)) • (v b).1 → a ≫ e = b ≫ e
  onto : ∀ {V : Scheme.{0}} (a₀ : V ⟶ W') (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ T')
    (h : (a ≫ ρ) ≫ c = (U.ι ≫ a₀) ≫ c) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧
      (g _ _ h : Matrix _ _ _).mulVec (v a).1 = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1)

def PBEx : Prop := ∀ (K : Type) [CommRing K] {W Z Y T : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z)
  (D : E.LineData Y) (d : ℕ), Nonempty (Blow q i π D d) → ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i →
  ∃ (P : PBData r d) (τ : P.T' ⟶ D.Y) (hτ : τ ≫ D.f = P.e ≫ j), ∀ {V : Scheme.{0}} (a b : V ⟶ P.T') (h : a ≫ P.e = b ≫ P.e)
    (h' : (a ≫ τ) ≫ D.f = (b ≫ τ) ≫ D.f), P.w a b h = (D.u _ _ h')⁻¹

def PBOf : Prop := In → ∀ (q : ℕ) [NeZero q] {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) (P : PBData r d), IsUnit (q : Γ(W, ⊤)) →
  ∀ (L : cech P.e ⟶ ofCat (glCat 1)) (ε : ℤˣ), (∀ (V : Scheme.{0}) (x : V ⟶ T) (a : Fin 2 → (V ⟶ P.T')) (h : ∀ s, a s ≫ P.e = x),
    lineUnit L (cechPt P.e 1 x a h) = P.w (a 0) (a 1) ((h 0).trans (h 1).symm) ^ (ε : ℤ)) →
  ∀ x : Ht q (sch.obj T) 2 1, pull _ (cechAug P.e) _ 2 x = c1 q L → PBT q d r x

def PBE : Prop := In → ∀ (q : ℕ) [NeZero q] (K : Type) [CommRing K], IsUnit (q : K) → ∀ {W Z Y T : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ), Nonempty (Blow p i π D d) →
  ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ L : cech D.f ⟶ ofCat (glCat 1), D.IsMap L →
  ∀ x : Ht q (sch.obj Y) 2 1, pull _ (cechAug D.f) _ 2 x = c1 q L →
    PBT q d r (pull _ (sch.map j) _ 2 x) ∧ ∀ U : Y.Opens, Off j U → pull _ (sch.map U.ι) _ 2 x = 0

def BlowE : Prop := ∀ (K : Type) [Field K] {W Z Y T : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z)
  (D : E.LineData Y) (d e : ℕ), Nonempty (Blow p i π D (d + 1)) → SmoothOfRelativeDimension (e + (d + 1)) p → IsProper π →
  ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → IsPair 1 (e + d) (π ≫ p) j ∧ IsProper r

def RegSeq : Prop := ∀ (A C : Type) [CommRing A] [CommRing C] (d : ℕ) (φ : MvPolynomial (Fin d) A →+* C), φ.Flat →
  ∀ a : Fin d → C, ∑ l, a l * φ (MvPolynomial.X l) ∈ Ideal.span (Set.range fun l => φ (MvPolynomial.X l)) ^ 2 →
    ∀ l, a l ∈ Ideal.span (Set.range fun l => φ (MvPolynomial.X l))

end UpperTheory.Gal.KunnethLefschetz.G
