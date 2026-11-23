import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.crystallineComparison

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {O K k : Type} [CommRing O] [Field K] [Field k] [Algebra O K] [Algebra O k]

abbrev fib (L : Type) [Field L] [Algebra O L] {Y : Scheme.{0}} (f : Y ⟶ Sp O) : Scheme.{0} :=
  pullback f (spMap (algebraMap O L))

def fibMap (L : Type) [Field L] [Algebra O L] {W Y : Scheme.{0}} (fW : W ⟶ Sp O) (fY : Y ⟶ Sp O) (g : W ⟶ Y)
    (hg : g ≫ fY = fW) : fib L fW ⟶ fib L fY :=
  pullback.map fW (spMap (algebraMap O L)) fY (spMap (algebraMap O L)) g (𝟙 _) (𝟙 _) (by simp [hg]) (by simp)

def coef (q j : ℕ) : ℤ := (-1) ^ j * (q : ℤ) ^ (j * (j - 1) / 2)

structure Datum (p f n : ℕ) (hp : p.Prime) {Y : Scheme.{0}} (fY : Y ⟶ Sp O) (Z : Fin (n + 1) → Scheme.{0})
    (p₁ p₂ : ∀ j, Z j ⟶ fib K fY) (hY : (p : Γ(fib k fY, ⊤)) = 0) where
  W : Scheme.{0}
  π : W ⟶ Y
  fin : IsFinite π
  surj : Surjective π
  flat : Flat (π ≫ fY)
  G : Type
  [grp : Group G]
  finG : Finite G
  ρ : G → (W ⟶ W)
  ρ_one : ρ 1 = 𝟙 W
  ρ_mul : ∀ a c, ρ (a * c) = ρ a ≫ ρ c
  ρ_over : ∀ a, ρ a ≫ π = π
  etK : Etale (fibMap K (π ≫ fY) fY π rfl)
  torsor : ∀ (L : Type) [Field L] [IsAlgClosed L] (y y' : Sp L ⟶ fib K (π ≫ fY)),
    y ≫ fibMap K (π ≫ fY) fY π rfl = y' ≫ fibMap K (π ≫ fY) fY π rfl →
      ∃! a, y ≫ fibMap K (π ≫ fY) (π ≫ fY) (ρ a) (by rw [← Category.assoc, ρ_over]) = y'
  I : Fin (n + 1) → Type
  finI : ∀ j, Fintype (I j)
  t : ∀ j, I j → (W ⟶ Y)
  t_over : ∀ j i, t j i ≫ fY = π ≫ fY
  s : ∀ j, I j → (fib K (π ≫ fY) ⟶ Z j)
  s₁ : ∀ j i, s j i ≫ p₁ j = fibMap K (π ≫ fY) fY π rfl
  s₂ : ∀ j i, s j i ≫ p₂ j = fibMap K (π ≫ fY) fY (t j i) (t_over j i)
  split : ∀ j, IsIso (Sigma.desc (f := fun _ : I j => fib K (π ≫ fY)) (fun i : I j =>
    (pullback.lift (s j i) (𝟙 (fib K (π ≫ fY))) (by rw [s₁ j i, Category.id_comp]) :
      fib K (π ≫ fY) ⟶ pullback (p₁ j) (fibMap K (π ≫ fY) fY π rfl))))
  A : Type
  finA : Fintype A
  Wa : A → Scheme.{0}
  ia : ∀ a, Wa a ⟶ fib k (π ≫ fY)
  closed : ∀ a, IsClosedImmersion (ia a)
  nilp : ∀ U : (fib k (π ≫ fY)).affineOpens,
    IsNilpotent (@Finset.prod A (Ideal Γ(fib k (π ≫ fY), U)) _ (@Finset.univ A finA)
      fun a => RingHom.ker ((ia a).app U).hom)
  es : ∀ a, (@Finset.sum (Fin (n + 1)) (FreeAbelianGroup (Wa a ⟶ fib k fY)) _ Finset.univ fun j =>
    coef (p ^ f) j • @Finset.sum (I j) _ _ (@Finset.univ (I j) (finI j)) fun i =>
      FreeAbelianGroup.of (ia a ≫ fibMap k (π ≫ fY) fY (t j i) (t_over j i) ≫
        GlobalTheory.SS.FrobField.absFrob (fib k fY) p (f * (n - j)) hp hY)) = 0

end GlobalTheory.crystallineComparison
