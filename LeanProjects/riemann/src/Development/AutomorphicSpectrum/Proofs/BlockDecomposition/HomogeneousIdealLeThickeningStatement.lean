import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_le_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal | exact GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal | (intros; apply GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal <;> assumption)
