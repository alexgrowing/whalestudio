import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBlowupCombinedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConesOfPhiDivisorStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

theorem coneZ_pull_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] (φs : InvFun ℤ) (X₁ X₂ : Type)
    [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁] [AddCommGroup X₂] [Module (𝓞 E) X₂]
    [Module.Finite (𝓞 E) X₂] (f : X₁ ≃ₗ[𝓞 E] X₂) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₂)
    (h : ConeZ E φs X₂ m γ) : ConeZ E φs X₁ m (fun i => pull f.toLinearMap (γ i)) := by
  haveI : Module.Finite ℤ X₂ := Module.Finite.trans (𝓞 E) X₂
  haveI : Module.Finite ℤ X₁ := Module.Finite.trans (𝓞 E) X₁
  exact IsCone.pull_equiv (bar := (id : ℤ → ℤ)) (φ := φs) h (f.restrictScalars ℤ)

theorem blowOrdSt : BlowOrdSt := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hfan hR hC hN4 hpol hd' hY hB
  have hA : IsPhiDiv (comb 0 φ (n * d') φ) Z EX := by
    intro W _ _ _ hW ϖ hϖ χ t μ P hχ be hbe hm
    by_cases hp : ∀ p : ℕ, p.Prime → IsUnit (p : W)
    · exact GlobalTheory.T.phi_divisor_arc_blowup E H D l Xo c X Z Y BY π e J EX n d' φ hY hB W hW hp ϖ hϖ χ t μ P hχ be hbe hm
    · exact GlobalTheory.T.polarization_blowup_combined E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hfan hR hC hN4 hpol hd' hY hB W hW hp
        ϖ hϖ χ t μ P hχ be hbe hm
  exact ⟨hA, GlobalTheory.T.cones_of_phi_divisor E H D l Xo c Z g φs 𝒩 φ EX (n * d') hg hfan hR
    (GlobalTheory.T.cone_conditions_product E H D l Xo c X Z π (ConeZ E φs) (coneZ_pull_equiv φs) hB.2.1 hB.2.2.1 hC) (Nat.mul_pos hB.1 hd') hA⟩

end GlobalTheory.TorRef
