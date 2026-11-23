import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverRestrictionBaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_restriction_base_change : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) (ι κ : Type) [LinearOrder ι] [Finite ι] [LinearOrder κ] [Finite κ]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (S : Type) [CommRing S] [Algebra S Γ(Y, ⊤)] (σ : R →+* S)
    (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (V : X.Opens) (W : Y.Opens) (U : ι → X.Opens) (U' : κ → Y.Opens)
    (hc : V ≤ ⨆ i, U i) (hc' : W ≤ ⨆ j, U' j) (hW : W ≤ g ⁻¹ᵁ V) (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ g ⁻¹ᵁ cechOpen V U (t.image τ))
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod W U' G) (n : ℕ)
    (z : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1)))
    (z' : LinearMap.ker (Cube.d (cechCube S G W U') (n + 1))),
    (∀ (t : {s : Finset κ // s.card = n + 1}) (ht : (t.1.image τ).card = n + 1),
      (z'.1 t : sectionsOn G (cechOpen W U' t.1)) = sortSign τ t.1 • sectionsOn.res S G (hτ t.1)
        (sectionsOn.mapOver hσ φ (cechOpen V U (t.1.image τ))
          (z.1 ⟨t.1.image τ, ht⟩ : sectionsOn F (cechOpen V U (t.1.image τ))))) →
    (∀ t : {s : Finset κ // s.card = n + 1}, (t.1.image τ).card ≠ n + 1 → z'.1 t = 0) →
    cechHEquivCohOn S hc' hG n (cechClass _ n z') = cohOn.pull hσ φ hW n (cechHEquivCohOn R hc hF n (cechClass _ n z)) := by
  first | exact @GlobalTheory.CompanionTheory.AltCech.cechHEquivCohOn_altPull | exact GlobalTheory.CompanionTheory.AltCech.cechHEquivCohOn_altPull | (intros; apply GlobalTheory.CompanionTheory.AltCech.cechHEquivCohOn_altPull <;> assumption)
