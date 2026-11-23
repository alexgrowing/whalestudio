import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.SSPf

def kbc {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) : pullback (k ≫ t) c ⟶ pullback t c :=
  pullback.map (k ≫ t) c t c k (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem kbc_fst {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) :
    pullback.fst (k ≫ t) c ≫ k = kbc k t c ≫ pullback.fst t c := by
  unfold kbc pullback.map
  rw [pullback.lift_fst]

def cechBC {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) : cech (kbc k t c) ⟶ cech k :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk (yoneda.map (kbc k t c))) (g := Arrow.mk (yoneda.map k))
    (yoneda.map (pullback.fst (k ≫ t) c)) (yoneda.map (pullback.fst t c))
    (by simp only [Arrow.mk_hom, ← Functor.map_comp, kbc_fst]))

def CechCmp : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S),
  IsIntegralHom k → Surjective k → IsUnit (q : Γ(S, ⊤)) → ∀ n : ℤ,
  Subsingleton (Hrel _ (cechBC k t c) (tw q i) n) → Subsingleton (Hrel _ (sch.map (pullback.fst t c)) (tw q i) n)

def CechFilt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (n : ℤ),
  (∀ p : ℕ, Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p))) → Subsingleton (Hrel R g F n)

def CechLevel : Prop := ∀ {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S), IsIntegralHom k →
  ∀ (p : ℕ) (R : Type) [CommRing R] (F : Shv R) (m : ℤ),
  (p = 0 → Subsingleton (Hrel R (sch.map (pullback.fst (k ≫ t) c)) F m)) →
  (0 < p → ∀ (W : Scheme.{0}) (w : W ⟶ X), IsIntegralHom w → Subsingleton (Hrel R (sch.map (pullback.fst (w ≫ t) c)) F m)) →
  Subsingleton (Hrel R (disc.map ((cechBC k t c).app (op (SimplexCategory.mk p)))) F m)

def SS : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S),
  IsIntegralHom k → Surjective k → IsUnit (q : Γ(S, ⊤)) → ∀ n : ℤ,
  (∀ m, Subsingleton (Hrel _ (sch.map (pullback.fst (k ≫ t) c)) (tw q i) m)) →
  (∀ (W : Scheme.{0}) (w : W ⟶ X), IsIntegralHom w → ∀ m < n,
    Subsingleton (Hrel _ (sch.map (pullback.fst (w ≫ t) c)) (tw q i) m)) →
  Subsingleton (Hrel _ (sch.map (pullback.fst t c)) (tw q i) n)

end LateralTheory.E.SSPf
