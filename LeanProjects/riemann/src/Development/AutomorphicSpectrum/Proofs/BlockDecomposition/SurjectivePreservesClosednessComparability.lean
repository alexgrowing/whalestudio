import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SurjPass

theorem aic_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Aic S) : Aic T := by
  intro P hP hdeg
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP
  obtain ⟨x, hx⟩ := h Q hQm (hQdeg ▸ hdeg)
  refine ⟨φ x, ?_⟩
  rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]

theorem comparable_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Val0 S) : Val0 T := by
  intro f g
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨g', rfl⟩ := hφ g
  obtain ⟨e, he, h1, h2⟩ := h f' g'
  refine ⟨φ e, ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, he.eq]
  · rw [Ideal.mem_span_singleton] at h1 ⊢
    rw [← map_mul]
    exact map_dvd φ h1
  · rw [Ideal.mem_span_singleton] at h2 ⊢
    rw [← map_one φ, ← map_sub, ← map_mul]
    exact map_dvd φ h2

theorem absolutely_closed_comparable_surjective : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T),
    Function.Surjective φ → (Aic S → Aic T) ∧ (Val0 S → Val0 T) := by
  intro S _ T _ φ hφ
  exact ⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩

end GlobalTheory.CompanionTheory.SurjPass
