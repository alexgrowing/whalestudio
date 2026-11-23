import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalizationIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normalization_iso : ∀ (K : Type) [Field K] [NumberField K] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 K)) (V : X.Opens), IsProjOver s →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme → Flat (V.ι ≫ s) →
    ∃ (N : Scheme.{0}) (ν : N ⟶ X), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N ∧ IsProjOver (ν ≫ s) ∧
      Flat (ν ≫ s) ∧ IsIso (ν ∣_ V) ∧ Dense ((ν ⁻¹ᵁ V : N.Opens) : Set N) := by
  first | exact @GlobalTheory.ProjBlowup.exists_normal_model_ringOfIntegers | exact GlobalTheory.ProjBlowup.exists_normal_model_ringOfIntegers | (intros; apply GlobalTheory.ProjBlowup.exists_normal_model_ringOfIntegers <;> assumption)
