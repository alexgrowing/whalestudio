import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleExtensionNormalBase
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_divisible_extension_normal_base : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X →
    ∀ (t₀ : SAB H (Sp (Kbar X))) (m₀ : SABMap t₀ tZ (genPt X ≫ g)), IsOfType Dw t₀ →
    ∀ (GG₀ : PDivGroup p (Kbar X)) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀)
      (ε₀ : (PDivGroup.mu p (Kbar X)).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ →
    ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)) (m : SABMap t tZ (U.toX ≫ g)),
      ∃ (GG : PDivGroup p U.Bp) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG)
        (ε : (PDivGroup.mu p U.Bp).Tate) (τ : Dw.La →+ GG.Tate),
        IsPropG Dw t GG act pol θ ε τ ∧ IsRestr m.φ act pol θ ε τ m₀.φ act₀ pol₀ θ₀ ε₀ τ₀ := by
  first | exact @GlobalTheory.GroupBplus.Aff.propG_affine | exact GlobalTheory.GroupBplus.Aff.propG_affine | (intros; apply GlobalTheory.GroupBplus.Aff.propG_affine <;> assumption)
