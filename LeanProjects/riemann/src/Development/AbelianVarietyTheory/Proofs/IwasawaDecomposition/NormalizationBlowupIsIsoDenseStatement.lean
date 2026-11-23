import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalization_blowup_isIso_dense : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (Z X' N V : Scheme.{0})
    (s : Z ⟶ Sp R) (b : X' ⟶ Z) (ν : N ⟶ X') (U : Z.Opens) (jV : V ⟶ pullback s (spMap (algebraMap R K))),
    IsLocallyNoetherian N → IsOpenImmersion jV → Dense (Set.range jV) →
    (∀ v, pullback.fst s (spMap (algebraMap R K)) (jV v) ∈ U) → IsIso (b ∣_ U) → IsIso (ν ∣_ (b ⁻¹ᵁ U)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ U) : N.Opens) : Set N) →
    ∃ jN : V ⟶ pullback (ν ≫ b ≫ s) (spMap (algebraMap R K)), IsOpenImmersion jN ∧ Dense (Set.range jN) ∧
      jN ≫ pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) = jV ∧
      pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ⁻¹' Set.range jV = Set.range jN := by
  first | exact @GlobalTheory.BlowOpen.lifts_to_normalisation | exact GlobalTheory.BlowOpen.lifts_to_normalisation | (intros; apply GlobalTheory.BlowOpen.lifts_to_normalisation <;> assumption)
