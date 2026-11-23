import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafA6suppPf

def LeafAWSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
  (α : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n)
  (β : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q j)) m),
  ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q (i + j))) (n + m),
    (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
    cup q (CohomologyClass.mk α : Ht q E n i) (CohomologyClass.mk β : Ht q E m j) = CohomologyClass.mk γ

def LeafRepVanish : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ (F : Shv R) (n : ℤ)
  (a : H R E F n), pull R f F n a = 0 →
  ∃ α : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk α = a ∧
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y), ev α.1 N w h Y ((f.app _).app _ y) = 0

def LeafCochainVanish : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (K : Cx R) (k : ℤ) (γ : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0) →
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) →
    γ = 0

theorem sub_map {U E : Spc} (f : U ⟶ E) {N : ℕ} {Y : Scheme.{0}} (y : Sx U N Y) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((f.app _).app _ y) j l h = (f.app _).app _ (Sx.sub y j l h) := by
  unfold Sx.sub
  have e := NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op Y)
  exact (ConcreteCategory.congr_hom e y).symm

theorem LeafA6supp_of (h1 : LeafAWSpec) (h2 : LeafRepVanish) (h3 : LeafCochainVanish) : LateralTheory.E.D2.LeafA6supp := by
  intro q _ U V E f g hc n m i j a b ha hb
  obtain ⟨α, rfl, hα⟩ := h2 (ZMod q) f hc.1 (tw q i) n a ha
  obtain ⟨β, rfl, hβ⟩ := h2 (ZMod q) g hc.2.1 (tw q j) m b hb
  obtain ⟨γ, hAW, hcup⟩ := h1 q E α β
  rw [hcup]
  have : γ.1 = 0 := by
    apply h3 (ZMod q) f g hc
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map f y 0 (p : ℕ), hα]
      simp
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map g y (p : ℕ) (N - p), hβ]
      simp
  have hγ : γ = 0 := Subtype.ext this
  rw [hγ]
  exact CohomologyClass.mk_zero _ _ _

end LateralTheory.E.LeafA6suppPf
