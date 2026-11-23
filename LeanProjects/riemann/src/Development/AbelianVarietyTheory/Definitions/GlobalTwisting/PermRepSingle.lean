import Mathlib

noncomputable section

open CategoryTheory

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def permRep (X : Type) [MulAction G X] (A : Rep k G) : Representation k G (X →₀ A.V) where
  toFun g := Finsupp.lmapDomain A.V k (g • ·) ∘ₗ Finsupp.mapRange.linearMap (A.ρ g)
  map_one' := by ext x a; simp
  map_mul' g h := by ext x a; simp [mul_smul]

@[simp] theorem permRep_single {X : Type} [MulAction G X] (A : Rep k G) (g : G) (x : X) (a : A.V) :
    permRep X A g (Finsupp.single x a) = Finsupp.single (g • x) (A.ρ g a) := by
  simp [permRep]

abbrev permT (X : Type) [MulAction G X] (A : Rep k G) : Rep k G := Rep.of (permRep X A)

variable (k G) in

abbrev perm (X : Type) [MulAction G X] : Rep k G := permT X (Rep.trivial k G k)

def permCoef (X : Type) [MulAction G X] {A B : Rep k G} (f : A ⟶ B) : permT X A ⟶ permT X B :=
  Rep.ofHom ⟨Finsupp.mapRange.linearMap f.hom.toLinearMap, fun g => by
    ext x a; simp [Rep.hom_comm_apply f]⟩

def permMap {X Y : Type} [MulAction G X] [MulAction G Y] (f : X → Y) (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (A : Rep k G) : permT X A ⟶ permT Y A :=
  Rep.ofHom ⟨Finsupp.lmapDomain A.V k f, fun g => by ext x a; simp [hf]⟩

def ptMap {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (A : Rep k G) :
    Rep.res φ A ⟶ Rep.res φ (permT X A) :=
  Rep.ofHom ⟨Finsupp.lsingle x, fun h => LinearMap.ext fun a => by
    change Finsupp.single x (A.ρ (φ h) a) = permRep X A (φ h) (Finsupp.single x a)
    rw [permRep_single, hx]⟩

variable (k) in

def ptH {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (n : ℕ) :
    groupHomology (Rep.trivial k H k) n ⟶ groupHomology (perm k G X) n :=
  groupHomology.map (A := Rep.trivial k H k) φ (ptMap φ x hx (Rep.trivial k G k)) n

abbrev hMap {A B : Rep k G} (f : A ⟶ B) (n : ℕ) : groupHomology A n ⟶ groupHomology B n :=
  groupHomology.map (MonoidHom.id G) f n

end GlobalTheory.HomStab

end
