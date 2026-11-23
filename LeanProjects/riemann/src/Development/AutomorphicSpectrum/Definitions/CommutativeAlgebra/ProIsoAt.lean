import Mathlib

namespace GlobalTheory.CompanionTheory.Ar

structure ProIso (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ n, 0 < n → ∀ x, (∃ y, a n x = n • y) ↔ ∃ y, x = n • y
  surj : ∀ n, 0 < n → ∀ y, ∃ x e, y = a n x + n • e
  isom : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ B' (a n x) (a n y) - B x y
  compat : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ e, a (n * m) x = a n x + n • e

structure ProIsoAt (p : ℕ) (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ k x, (∃ y, a k x = p ^ k • y) ↔ ∃ y, x = p ^ k • y
  surj : ∀ k y, ∃ x e, y = a k x + p ^ k • e
  isom : ∀ k x y, ((p : ℤ) ^ k) ∣ B' (a k x) (a k y) - B x y
  compat : ∀ k x, ∃ e, a (k + 1) x = a k x + p ^ k • e

variable {O : Type} [CommRing O] {L L' L'' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] [AddCommGroup L''] [Module O L''] {B : LinearMap.BilinForm ℤ L}
  {B' : LinearMap.BilinForm ℤ L'} {B'' : LinearMap.BilinForm ℤ L''}

def ProIso.ofEquiv (e : L ≃ₗ[O] L') (h : ∀ x y, B' (e x) (e y) = B x y) : ProIso O B B' where
  a _ := e.toLinearMap
  inj n _ x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      simpa [map_nsmul] using hy
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [map_nsmul]⟩
  surj n _ y := ⟨e.symm y, 0, by simp⟩
  isom n _ x y := by simp [h]
  compat n m _ _ x := ⟨0, by simp⟩

def ProIso.trans (f : ProIso O B B') (g : ProIso O B' B'') : ProIso O B B'' where
  a n := (g.a n).comp (f.a n)
  inj n hn x := by
    rw [← f.inj n hn, ← g.inj n hn]
    rfl
  surj n hn z := by
    obtain ⟨y, e, rfl⟩ := g.surj n hn z
    obtain ⟨x, e', rfl⟩ := f.surj n hn y
    exact ⟨x, g.a n e' + e, by simp [map_nsmul, add_assoc]⟩
  isom n hn x y := by
    have := dvd_add (g.isom n hn (f.a n x) (f.a n y)) (f.isom n hn x y)
    simpa using this
  compat n m hn hm x := by
    obtain ⟨e, he⟩ := f.compat n m hn hm x
    obtain ⟨e', he'⟩ := g.compat n m hn hm (f.a (n * m) x)
    refine ⟨g.a n e + e', ?_⟩
    simp only [LinearMap.comp_apply]
    rw [he', he]
    simp [map_nsmul, add_assoc]

def ProIso.IsInv (f : ProIso O B B') (g : ProIso O B' B) : Prop :=
  (∀ n, 0 < n → ∀ x, ∃ e, g.a n (f.a n x) = x + n • e) ∧ ∀ n, 0 < n → ∀ y, ∃ e, f.a n (g.a n y) = y + n • e

end GlobalTheory.CompanionTheory.Ar
