import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystem
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_vanishing_ideal_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family | exact GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family | (intros; apply GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family <;> assumption)
