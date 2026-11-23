import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) / ((∑ i, ‖z ⟨q.1, i⟩‖ ^ 2 : ℝ) : ℂ)

def Pts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k × ι k) → ℂ) :=
  proj '' conePts P

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

def rep (x : Pts P) : (Σ k, ι k) → ℂ := x.2.choose

theorem rep_mem (x : Pts P) : rep x ∈ conePts P := x.2.choose_spec.1

theorem proj_rep (x : Pts P) : proj (rep x) = x.1 := x.2.choose_spec.2

variable (P) in

def src (p : (k : K) → ι k) : Set (Pts P) := {x | ∀ k, rep x ⟨k, p k⟩ ≠ 0}

variable (P) in

def coord (p : (k : K) → ι k) (x : Pts P) : Fin (Fintype.card (Σ k, ι k)) → ℂ :=
  renPt (affCoord p (rep x))

variable (P) in

def ideal (p : (k : K) → ι k) : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  (chartIdeal P p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)

open Classical in

def lift (p : (k : K) → ι k) (q : Σ k, ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  if q.2 = p q.1 then 1 else X (Fintype.equivFin (Σ k, ι k) q)

variable (P) in

def bd (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  ((chartIdeal (P ⊔ D) p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).radical

theorem finite_minimalPrimes (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

variable (P) in

def rc (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : ℕ := (finite_minimalPrimes (P ⊔ D)).toFinset.card

variable (P) in

def compIdeal (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).1

variable (P) in

def comp (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Set (Pts P) :=
  {x | ∀ f ∈ compIdeal P D k, eval (rep x) f = 0}

def ordAlong (Q P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) : ℕ :=
  sSup {m : ℕ | ∃ s ∉ Q, s * f ∈ Q ^ m ⊔ P}

theorem compIdeal_mem (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) :
    compIdeal P D k ∈ (P ⊔ D).minimalPrimes := by
  exact (Set.Finite.mem_toFinset _).1 ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).2

theorem eval_lift (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    eval (coord P p x) (lift p q) = affCoord p (rep x) q := by
  classical
  unfold lift
  split_ifs with h
  · obtain ⟨k, i⟩ := q
    simp only at h
    subst h
    simp [affCoord, hx k]
  · simp [coord, renPt]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
