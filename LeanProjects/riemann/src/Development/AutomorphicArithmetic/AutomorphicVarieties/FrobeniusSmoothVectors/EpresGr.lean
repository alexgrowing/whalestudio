import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def pq (a : Fin 3) : ZMod 2 := ((w 3 a : ℤ) : ZMod 2)

theorem pw_eq (a b : Fin 3) : pw a b = pq a - pq b := Int.cast_sub _ _

def GrM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (α β : Fin 3 → ZMod 2)
    (M : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, M a b ∈ evp σ (α a - β b)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

namespace Box

structure Gr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (B : Box F 3 R) (σ : R →ₐ[O] R)
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ pq pq (B.r s).mat
  g : ∀ v, GrM σ (π v) pq (B.g v : Matrix (Fin 3) (Fin 3) R)

variable {K : Type} [CommRing K]

structure Ev (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, (B.r s).mat ∈ adp K 0
  g : ∀ v a b, π v a ≠ pq b → (B.g v : Matrix (Fin 3) (Fin 3) K) a b = 0
  stab : ∀ j s, adp K j ≤ (adp K j).comap (B.ad s)

variable {B : Box F 3 K} {π : F.V → Fin 3 → ZMod 2}

def Ev.ad (h : B.Ev π) (j : ZMod 2) : Representation K F.Γ (adp K j) := B.ad.subrepresentation (adp K j) (h.stab j)

@[simp] theorem Ev.ad_apply (h : B.Ev π) (j : ZMod 2) (s : F.Γ) (X : adp K j) :
    ((h.ad j s X : adp K j) : Matrix (Fin 3) (Fin 3) K) = B.ad s X := rfl

variable (B) in

def bp (j : ZMod 2) (v : F.V) : Submodule K (adp K j) := (B.b v).comap (adp K j).subtype

end Box

section CO

variable {O : Type} [CommRing O] [IsLocalRing O] {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C]
  [Algebra O C]

structure SetLift.Gr {p : C' →ₐ[O] C} {B : Box F 3 C} (D : SetLift p B) (σ' : C' →ₐ[O] C')
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ' pq pq (D.r s : Matrix (Fin 3) (Fin 3) C')
  g : ∀ v, GrM σ' (π v) pq (D.g v : Matrix (Fin 3) (Fin 3) C')
  t : ∀ v s, GrM σ' (π v) (π v) (D.t v s : Matrix (Fin 3) (Fin 3) C')

def formp (σ' : C' →ₐ[O] C') (K : Ideal C') (j : ZMod 2) :
    Submodule (ResidueField O) (K →ₗ[O] ResidueField O) where
  carrier := {u | ∀ i, i ≠ j → ∀ y : K, (y : C') ∈ evp σ' i → u y = 0}
  add_mem' h h' i e y hy := by simp [h i e y hy, h' i e y hy]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c u h i e y hy := by simp [h i e y hy]

variable (O) in

def HasObsG {R : Type} [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) (H : Type) [AddCommGroup H]
    [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (σ' : C' →ₐ[O] C'), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ → (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) →
    ∃ ob : formp σ' (RingHom.ker p) j →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u.1 y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

end CO

end UpperTheory.V.Fr
