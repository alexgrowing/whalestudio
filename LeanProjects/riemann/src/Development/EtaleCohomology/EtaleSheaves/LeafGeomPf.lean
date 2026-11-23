import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2

namespace LateralTheory.E.LeafGeomPf

def vec0 {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Fin (a + b) → Scheme.Γ.obj (op X) :=
  ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
    ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).1

def First {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin a => vec0 V W x (Fin.castAdd b i)) = ⊤

def Second {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin b => vec0 V W x (Fin.natAdd a i)) = ⊤

def LeafHalf1 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V), Mono f₁ ∧
    p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), First V W x → ∃ y : Sx U₁ n X, (f₁.app _).app _ y = x

def LeafHalf2 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₂ : Spc) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₂ : U₂ ⟶ PB W), Mono f₂ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), Second V W x → ∃ y : Sx U₂ n X, (f₂.app _).app _ y = x

def LeafLocal : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) (n : ℕ) (X : Scheme.{0})
  (x : Sx (PB (bsumOf V W)) n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    First V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) ∨
    Second V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) (hL : LeafLocal) : LateralTheory.E.D2.LeafGeom := by
  intro E a b V W
  obtain ⟨U₁, f₁, p₁, m₁, e₁, l₁, s₁⟩ := h1 V W
  obtain ⟨U₂, f₂, p₂, m₂, e₂, l₂, s₂⟩ := h2 V W
  refine ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, ?_, e₁, l₁, e₂, l₂⟩
  intro n X x
  obtain ⟨S, hS, hk⟩ := hL V W n X x
  refine ⟨S, hS, fun Y k hk' => ?_⟩
  rcases hk Y k hk' with h | h
  · exact Or.inl (s₁ n Y _ h)
  · exact Or.inr (s₂ n Y _ h)

end LateralTheory.E.LeafGeomPf
