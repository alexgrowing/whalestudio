import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u v' u'

namespace GlobalTheory.CatH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

abbrev Cn (n : ℕ) : Type (max u v) := ∀ s : ComposableArrows C n, F.obj (s.obj (Fin.last n))

def face {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) : ComposableArrows C n :=
  (Fin.succAboveOrderEmb i).monotone.functor ⋙ s

def toLast {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) :
    (face i s).obj (Fin.last n) ⟶ s.obj (Fin.last (n + 1)) :=
  s.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))

def d (n : ℕ) : Cn F n →ₗ[R] Cn F (n + 1) where
  toFun f s := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def Bn : ∀ n : ℕ, Submodule R (Cn F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d F n)

abbrev H (n : ℕ) : Type (max u v) := LinearMap.ker (d F n) ⧸ (Bn F n).submoduleOf (LinearMap.ker (d F n))

variable {F} {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

structure Mor (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R') (σ : R →+* R') where

  G : C' ⥤ C

  τ : ∀ T : C', F.obj (G.obj T) →ₛₗ[σ] F'.obj T
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : F.obj (G.obj T)), τ T' ((F.map (G.map φ)).hom x) = (F'.map φ).hom (τ T x)

namespace Mor

def id (F : C ⥤ ModuleCat.{0} R) : Mor F F (RingHom.id R) where
  G := 𝟭 C
  τ _ := LinearMap.id
  nat _ _ := rfl

def restrict (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) : Mor F (G ⋙ F) (RingHom.id R) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

def ofNatTrans {F₁ : C ⥤ ModuleCat.{0} R} (α : F ⟶ F₁) : Mor F F₁ (RingHom.id R) where
  G := 𝟭 C
  τ T := (α.app T).hom
  nat φ x := by
    change ((F.map φ ≫ α.app _).hom) x = ((α.app _ ≫ F₁.map φ).hom) x
    rw [α.naturality]

variable (m : Mor F F' σ)

def pullC (n : ℕ) : Cn F n →ₛₗ[σ] Cn F' n where
  toFun f s := m.τ _ (f (s ⋙ m.G))
  map_add' f g := funext fun s => map_add (m.τ _) _ _
  map_smul' r f := funext fun s => LinearMap.map_smulₛₗ (m.τ _) _ _

theorem d_pullC (n : ℕ) (f : Cn F n) : d F' n (m.pullC n f) = m.pullC (n + 1) (d F n f) := by
  funext s
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F'.map (toLast i s)).hom (m.τ _ (f (face i s ⋙ m.G))) =
    m.τ _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (m.G.map (toLast i s))).hom (f (face i s ⋙ m.G)))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, m.nat]

def pullZ (n : ℕ) : LinearMap.ker (d F n) →ₛₗ[σ] LinearMap.ker (d F' n) :=
  ((m.pullC n).domRestrict _).codRestrict _ fun f => by
    change d F' n (m.pullC n f.1) = 0
    rw [m.d_pullC, f.2, map_zero]

def pull (n : ℕ) : H F n →ₛₗ[σ] H F' n :=
  Submodule.mapQ _ _ (m.pullZ n) (by
    intro f hf
    change m.pullC n f.1 ∈ Bn F' n
    have hf' : f.1 ∈ Bn F n := hf
    cases n with
    | zero =>
      have : f.1 = 0 := hf'
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g, hg⟩ := hf'
      exact ⟨m.pullC n g, by rw [m.d_pullC, hg]⟩)

end Mor

example (n : ℕ) (f : Cn F n) (s : ComposableArrows C n) : (Mor.id F).pullC n f s = f s := rfl

example : Bn F 0 = ⊥ := rfl

example (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (F.map (toLast 0 s)).hom (f (face 0 s)) - (F.map (toLast 1 s)).hom (f (face 1 s)) := by
  simp [d, Fin.sum_univ_two, sub_eq_add_neg]

end GlobalTheory.CatH
