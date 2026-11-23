import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

open NumberField UpperTheory.V.KL

namespace UpperTheory.V.ZK.Up

def rq (q : ℕ) (G : Type) (m : ℕ) : Ch ℤ G m →+ Ch (ZMod q) G m :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod q))

structure IsCls (k : ℕ) (cls : ∀ (G : Type) [Group G], LinearMap.ker (bd ℤ G k) →+ grpH G (k + 1)) : Prop where
  surj : ∀ (G : Type) [Group G], Function.Surjective (cls G)
  zero : ∀ (G : Type) [Group G] (z : LinearMap.ker (bd ℤ G k)), cls G z = 0 ↔ Bd z.1
  nat : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (z : LinearMap.ker (bd ℤ G k)) (z' : LinearMap.ker (bd ℤ H k)),
    z'.1 = cm ℤ f (k + 1) z.1 → cls H z' = (grpHMap f (k + 1)).hom (cls G z)

def Bridge : Prop := ∀ k : ℕ, ∃ cls, IsCls k cls

def RqFacts : Prop :=
  ∀ q : ℕ,
    (∀ (G : Type) [Group G] (m : ℕ) (z : Ch ℤ G (m + 1)), bd (ZMod q) G m (rq q G (m + 1) z) = rq q G m (bd ℤ G m z)) ∧
    (∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch ℤ G m),
      cm (ZMod q) f m (rq q G m z) = rq q H m (cm ℤ f m z)) ∧
    (∀ (G : Type) (m : ℕ), Function.Surjective (rq q G m)) ∧
    ∀ (G : Type) (m : ℕ) (z : Ch ℤ G m), rq q G m z = 0 ↔ ∃ w, z = q • w

def TorsStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ m n n' : ℕ, 2 * m + 4 ≤ n → n ≤ n' →
    Finite (AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m)) ∧
      Nat.card (AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m)) = tc L n m

structure IsPrimH {R B : Type} [CommRing R] [AddCommGroup B] {m : ℕ} (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) : Prop where
  stab : ∀ n n' (h : n ≤ n') x, φ n' ((grpHMap (stab R n n' h) m).hom x) = φ n x
  psi : ∀ d n x, φ (d * n) ((grpHMap (psi R d n) m).hom x) = d • φ n x

def Descend : Prop :=
  ∀ (R : Type) [CommRing R] (q k : ℕ) (B : Type) [AddCommGroup B] [Module (ZMod q) B]
    (Φ : ∀ n : ℕ, Ch (ZMod q) (GL (Fin n) R) (k + 1) →ₗ[ZMod q] B), IsPrimFam Φ →
      ∃ φ : ∀ n : ℕ, grpH (GL (Fin n) R) (k + 1) →+ B, IsPrimH φ ∧
        ∀ n (z : Ch ℤ (GL (Fin n) R) (k + 1)), Cyc z → ∃ x, φ n x = Φ n (rq q _ (k + 1) z)

def ZVal : Prop :=
  ∀ (R B : Type) [CommRing R] [AddCommGroup B] (m l ν : ℕ) (hl : 0 < l), (∀ b : B, l ^ ν • b = 0) →
    ∀ φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B, IsPrimH φ → ∀ n t : ℕ, ∃ u : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      l ^ t • φ n x = φ (lev l n t) (u • zSeq R hl x t)

def RankCount : Prop :=
  ∀ (H B : Type) [AddCommGroup H] [AddCommGroup B] (q r : ℕ), 0 < q → (∀ b : B, q • b = 0) →
    Finite (AddCommGroup.torsion H) → ∀ (J : Submodule ℤ H), Module.rank ℤ J ≤ r → ∀ (f : H →+ B) (S : Finset B),
      (∀ s ∈ S, ∃ x ∈ J, s = f x) → S.card ≤ q ^ r * Nat.card (AddCommGroup.torsion H)

def Bock : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (G : Type) [Group G] (k : ℕ),
    ∃ β : LinearMap.ker (bd (ZMod q) G k) →+ AddCommGroup.torsion (grpH G k),
      ∀ y, β y = 0 → ∃ z : Ch ℤ G (k + 1), Cyc z ∧ rq q G (k + 1) z = y.1

def FibCount : Prop :=
  ∀ (Y T B : Type) [AddCommGroup Y] [AddCommGroup T] [AddCommGroup B] [Finite T] (β : Y →+ T) (g : Y →+ B) (c : ℕ),
    (∀ S : Finset B, (∀ s ∈ S, ∃ y, β y = 0 ∧ s = g y) → S.card ≤ c) →
      ∀ S : Finset B, (∀ s ∈ S, ∃ y, s = g y) → S.card ≤ c * Nat.card T

end UpperTheory.V.ZK.Up

end
