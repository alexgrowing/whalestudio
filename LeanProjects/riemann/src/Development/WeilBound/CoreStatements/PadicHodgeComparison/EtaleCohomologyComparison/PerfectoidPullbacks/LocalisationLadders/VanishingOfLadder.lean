import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrameStatement

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

theorem sq_sub {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C)
    (h : a.S T ≤ b.S T) : Subsingleton ((sq a b).obj T) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have h0 : ∀ z ∈ sqM a b T, z = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hz
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h hw)
  exact Subtype.ext ((h0 x hx).trans (h0 y hy).symm)

theorem Poly.Ladder.mono {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ}
    {a b : ℤ → IdF Φ.A} {r r' : ℤ} (h : Q.Ladder a b r) (hr : r' ≤ r) : Q.Ladder a b r' :=
  ⟨h.le, fun r'' h' => h.ca r'' (h'.trans hr), fun r'' h' => h.cb r'' (h'.trans hr)⟩

theorem vanishing_of_ladder (d : ℕ) : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ)
    {a b : ℤ → IdF Φ.A} (E : Frame Φ d) (r : ℤ), Q.Ladder a b r →
    (∀ r', r - d ≤ r' → r' ≤ r → (a r').S E.D ≤ (b r').S E.D) → ∀ j, Subsingleton (CH.H (sq (a r) (b r)) j) := by
  induction d with
  | zero =>
    intro R _ C _ Φ Q a b E r hQ h j
    exact GlobalTheory.T.cohomology_vanishing_of_trivial_frame E (sq (a r) (b r)) (sq_sub _ _ _ (h r (by simp) le_rfl)) j
  | succ d ih =>
    intro R _ C _ Φ Q a b E r hQ h
    let σ : ∀ T : C, E.D ⟶ T := fun T => Classical.choice (E.ne T)
    obtain ⟨β, hi, hx, hs, -⟩ := GlobalTheory.T.filtration_critical_comparison_map Q E a b r (fun r' T => hQ.le r' T) (hQ.ca r le_rfl)
      (hQ.ca (r - 1) (by omega)) (hQ.cb r le_rfl) (hQ.cb (r - 1) (by omega))
    have hcut : ∀ r'' : ℤ, r'' ≤ r → r - (d + 1 : ℕ) ≤ r'' - d → ∀ j,
        Subsingleton (CH.H (Cut.Pσ Q σ ⋙ Cut.U E ⋙ sq (a r'') (b r'')) j) := by
      intro r'' hr hr' j
      have h1 : Subsingleton (CH.H (Cut.U E ⋙ sq (a r'') (b r'')) j) :=
        ih (Cut.Q1 Q) (Cut.E1 E) r'' (Cut.ladder_truncation Q (hQ.mono hr)) (fun r' h1 h2 => h r' (by omega) (by omega)) j
      exact (CrystallineSemistableComparison.P.adj (Cut.U E ⋙ sq (a r'') (b r'')) (Cut.Pσ Q σ) (Cut.U E) (Cut.adjPσ Q σ) j).2.subsingleton
    exact GlobalTheory.T.cohomology_vanishing_short_exact (Functor.whiskerLeft (Pt.Sσ σ) (Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))))
      (Functor.whiskerLeft (Pt.Sσ σ) β) (fun T => hi _) (fun T => hx _) (fun T => hs _)
      (hcut r le_rfl (by omega)) (hcut (r - 1) (by omega) (by omega))

end CrystallineSemistableComparison.Pb
