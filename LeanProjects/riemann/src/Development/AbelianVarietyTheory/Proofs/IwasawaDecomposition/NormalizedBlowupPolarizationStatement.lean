import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupPolarization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_blowup_polarization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k n : ℕ)
    (ρ : gen Y ⟶ gen X) (X' N : Scheme.{0}) (b : X' ⟶ X.X) (ν : N ⟶ X'),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) → 0 < n →
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) = (BY.idealSheaf ^ n).comap (genι Y) →
    FinalTheorems.Blowup b (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)) → IsFinite ν →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N →
    IsIso (ν ∣_ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl) : N.Opens) : Set N) →
    ∃ e : gen Y ≅ pullback (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)),
      e.hom ≫ pullback.snd _ _ = genStr Y ∧ e.hom ≫ pullback.fst _ _ ≫ ν ≫ b = ρ ≫ genι X := by
  first | exact @GlobalTheory.TorRef.genFibre_normBlowup_iso | exact GlobalTheory.TorRef.genFibre_normBlowup_iso | (intros; apply GlobalTheory.TorRef.genFibre_normBlowup_iso <;> assumption)
