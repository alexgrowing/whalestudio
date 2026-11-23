import Mathlib

namespace Formalism.SL.IwahoriBlocks

variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]

def IsHerm (h : V →ₗ[E] V →ₗ⋆[E] E) : Prop := ∀ v w, h w v = star (h v w)

def eich (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v : V) : V :=
  v + h v u • x - h v x • (u + s • x)

def EichIsom : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v w, h (eich h x u s v) (eich h x u s w) = h v w

def EichInv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v, eich h x (-u) (star s) (eich h x u s v) = v ∧ eich h x u s (eich h x (-u) (star s) v) = v

def EichComp : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x a b : V) (s t : E),
    IsHerm h → h x x = 0 → h a x = 0 → h b x = 0 →
    ∀ v, eich h x a s (eich h x b t v) = eich h x (a + b) (s + t + h b a) v

def EichShift : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s c : E),
    ∀ v, eich h x (u + c • x) s v = eich h x u (s + c - star c) v

def EichEquiv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (g : V →ₗ[E] V), (∀ v w, h (g v) (g w) = h v w) →
    ∀ (x u : V) (s : E) (v : V), g (eich h x u s v) = eich h (g x) (g u) s (g v)

def EichMove : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ v, h v x' = 0 →
      eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x)

def EichNew : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    (h u x = 0 → eich h x u s u = u + h u u • x) ∧
    (h x' u = 0 → eich h x u s x' = x' - h x' x • (u + s • x))

def EichPair : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ y z, h y x = 0 → h y u = 0 → h z x' = 0 →
      h y (eich h x u s (eich h x' u s z)) = h y z + star (h z u) * h y x'

def EichInt : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (x x' u : V) (s : E),
    IsHerm h →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    u ∈ abelian₂ → x + x' ∈ abelian₂ → s • x ∈ abelian₂ → h x' x ∈ O → h u x = 0 → h u x' = 0 →
    ∀ v ∈ abelian₂, h v x' = 0 → eich h x u s (eich h x' u s v) ∈ abelian₂

end Formalism.SL.IwahoriBlocks
