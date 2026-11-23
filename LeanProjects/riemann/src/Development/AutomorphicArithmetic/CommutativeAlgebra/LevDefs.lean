import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace UpperTheory.Lev

variable {G : GDatum}

def MN (n : ℕ) (a b : G.La) : Prop := ∃ c : G.La, a = b + n • c

structure IsLSim (n : ℕ) (f : G.La → G.La) (ν : ℤ) : Prop where
  add : ∀ x y, MN n (f (x + y)) (f x + f y)
  lin : ∀ (c : G.O) x, MN n (f (c • x)) (c • f x)
  inj : ∀ x, MN n (f x) 0 → MN n x 0
  surj : ∀ y, ∃ x, MN n (f x) y
  cop : IsCoprime ν (n : ℤ)
  isom : ∀ x y, (n : ℤ) ∣ 2 * G.EF (f x) (f y) - ν * (2 * G.EF x y)

structure GSim (G : GDatum) where
  f : ℕ → G.La → G.La
  ν : ℕ → ℤ
  sim : ∀ n, 0 < n → IsLSim n (f n) (ν n)
  tower : ∀ n m : ℕ, 0 < n → 0 < m → ∀ x, MN n (f (n * m) x) (f n x)
  νtower : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n

variable {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

abbrev TAt {gb : GBase G R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) {K : Type} [Field K] (x : Sp K ⟶ S) : Type :=
  GTateIso G K (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def GLift {gb : GBase G R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) (k : ℕ) (T : Over S)
    (lv : G.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ x, lv ((N * k) • x) = 1) ∧
  (∀ (c : G.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧ (∀ x, lv (k • x) = toUnit T ≫ o.eta x) ∧
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left), ∃ I : TAt o (x ≫ T.hom),
    ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev (N * k) y

end UpperTheory.Lev
