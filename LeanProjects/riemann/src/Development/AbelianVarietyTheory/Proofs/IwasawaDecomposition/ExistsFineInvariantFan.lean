import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCmStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAutStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothProjectiveRefinementPolyFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransferStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunctionStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_fine_invariant_fan {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {g q : ℕ} {φs : InvFun ℤ}
    (hφ : IsPolFan (id : ℤ → ℤ) g φs) (hq : Module.finrank ℚ E * q ≤ g) (𝒩 : Finset ℕ) (h𝒩 : ∀ N ∈ 𝒩, 1 ≤ N) :
    ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ IsPosFn H φ' ∧
      (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ'.toFun n (fun a b => k * B a b) = k * φ'.toFun n B) ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ →
          (restr (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ := by
  classical

  have hpoly : IsPolyFan H.bar q (baseFun (𝓞 E) (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1))) := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.polarisationBaseFunction_properties E H g q φs (𝒩.image (· - 1)) X hφ hq hX
    exact ⟨h1, h2, h3, h4, GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut E H g q φs (𝒩.image (· - 1)) X hφ hq hX (GlobalTheory.T.hasPolyhedralCover_balancedForms_CMField E H X)⟩
  have htw : IsTwInv H (baseFun (𝓞 E) (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1))) := by
    intro σ _ n B
    exact baseFun_twist _ _ _ σ n B
  have hdom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X := by
    intro X _ _ _ _
    exact GlobalTheory.T.dominatesLinearFormsOnBalancedForms_cm E H X
  obtain ⟨φ', h1, h2, h3, hlin⟩ := GlobalTheory.T.exists_invariant_smoothProjective_refinement_polyFan E H q _ hdom hpoly htw
  obtain ⟨φ'', k1, k2, k3, k4, k5, kcone⟩ := GlobalTheory.T.exists_homogeneous_positive_polFan_extension E H q φ' h1 h2 h3
  refine ⟨φ'', k1, k2, k3, k4, k5, ?_⟩
  intro X _ _ _ _ hX m γ hγ
  have hc : IsCone H.bar φ' γ := kcone X hX m γ hγ
  obtain ⟨hr, hf⟩ := GlobalTheory.T.linearOn_isFine_of_linearOn_polarisationBaseFunction E H g q (fineDen g (𝒩.image (· - 1))) φs (𝒩.image (· - 1)) X
    (fineDen_pos g _) hφ hq hX m γ hc.mem hc.nonneg (hlin X hX m γ hc)
  refine ⟨hr, fun N hN => ?_⟩
  have hfN := hf (N - 1) (Finset.mem_image_of_mem _ hN)
  rwa [Nat.sub_add_cancel (h𝒩 N hN)] at hfN

end GlobalTheory.PolFan
