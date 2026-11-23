import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
namespace GlobalTheory.AdditiveBiext
variable {R : Type} [CommRing R] {d : ℕ}
lemma comp1_scalar {n : ℕ} (a : R) (p : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) :
    comp1 (fun i => (C a * X ((0:Fin 1), i) : PS R 1 d)) p = fun i => C a * p i := by
  funext i
  have h : ∀ (j : Fin 1) (l : Fin d), constantCoeff ((![p] : Fin 1 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j; simpa using hp l
  unfold comp1
  rw [ev_mul _ h, ev_C, ev_X _ h]; simp
lemma addLaw_add {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) :
    (addLaw R d).add p q = fun i => p i + q i := by
  funext i
  have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![p, q] : Fin 2 → Pt R n d) j l) = 0 := by
    intro j l; fin_cases j
    · simpa using hp l
    · simpa using hq l
  show ev ![p, q] (X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) = _
  rw [ev_add _ h, ev_X _ h, ev_X _ h]; simp

def scalarAct (R : Type) [CommRing R] (d : ℕ) : OAct R (addLaw R d) where
  act := fun a i => C a * X ((0:Fin 1), i)
  const := by intro a i; simp
  hom := by
    intro a
    rw [addLaw_add _ _ (by simp [pt]) (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), comp1_scalar _ _ (by simp [pt]), addLaw_add _ _ (by simp [pt]) (by simp [pt])]
    funext i; ring
  add_act := by
    intro a b
    rw [addLaw_add _ _ (by simp) (by simp)]
    funext i; rw [map_add]; ring
  mul_act := by
    intro a b
    rw [comp1_scalar _ _ (by simp)]
    funext i; rw [map_mul]; ring
  one_act := by funext i; simp [pt]

def additiveFB (R : Type) [CommRing R] [StarRing R] (d : ℕ) : FB R d R := FB.triv (addLaw R d) (scalarAct R d)

theorem main : ∀ (R : Type) [CommRing R] [StarRing R] (d : ℕ), ∃ B : FB R d R,
    (∀ i, B.G.F i = X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) ∧ ∀ a i, B.A.act a i = C a * X ((0 : Fin 1), i) :=
  fun R _ _ d => ⟨additiveFB R d, fun _ => rfl, fun _ _ => rfl⟩
end GlobalTheory.AdditiveBiext
