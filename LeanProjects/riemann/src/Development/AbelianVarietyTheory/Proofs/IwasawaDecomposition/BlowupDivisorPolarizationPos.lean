import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMultipleRationalSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormConeRefinementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationRefinedFanLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorLocalEquationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MixedLower

theorem chartMem_of_blow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → GlobalTheory.MixedLower.ChartMem (ConeZ E φs) X J φ (n * d') := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB
  unfold ChartMem
  intro R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn W _ _ _ hW _ ϖ hϖ f _ _ be hbe hFA m hm
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have hrk := GlobalTheory.CharRank.finrank_le_min E H D l Xo c X R ξ t mξ P hCN hEt hFU hTI
  have hbal : be ∈ balForms H.bar P.D.toPre.X := by rw [balForms_eq_levelForms]; exact hbe
  have hpsd : ∀ y, 0 ≤ be y y := fun y => by
    obtain ⟨r, n₀, -, h, -⟩ := hFA y
    rw [h]; positivity
  have hcone : GlobalTheory.ChartMono.InRealCone γ be := hIn W hW ϖ hϖ f be hbal.1 hFA
  obtain ⟨k₁, δ, hδ, hbeδ, hspan⟩ := GlobalTheory.T.balanced_form_cone_refinement E H (min D.p D.q) g φs 𝒩 φ P.D.toPre.X k' γ hg hφs hRef hrk hCone be hbal hpsd hcone
  have hfan : IsPolFanOn H.bar φ P.D.toPre.X := hRef.1 P.D.toPre.X hrk
  obtain ⟨ℓ, hℓbe, hℓ⟩ := GlobalTheory.T.cone_multiple_rational_span E H φ P.D.toPre.X k₁ δ (n * d') {β | β ∈ balForms H.bar P.D.toPre.X ∧ GlobalTheory.ChartMono.InRealCone γ β}
    hfan hδ (fun β hβ => hspan β hβ.1 hβ.2) be hbeδ
  have hφ0 : ∀ β : LinearMap.BilinForm ℤ P.D.toPre.X, 0 ≤ φ.evalZ β := fun β => hRef.2.2.2.2.1.2 _ _
  have hℓ' : ∀ β ∈ balForms H.bar P.D.toPre.X, (∀ y, 0 ≤ β y y) → GlobalTheory.ChartMono.InRealCone γ β →
      ((n * d' : ℕ) : ℝ) * φ.evalZ β ≤ ℓ β := fun β h1 h2 h3 => hℓ β ⟨h1, h3⟩ h1 h2
  have hℓ0 : ∀ β ∈ balForms H.bar P.D.toPre.X, (∀ y, 0 ≤ β y y) → GlobalTheory.ChartMono.InRealCone γ β → 0 ≤ ℓ β :=
    fun β h1 h2 h3 => by
      have := hℓ' β h1 h2 h3
      have : (0 : ℝ) ≤ ℓ β := le_trans (mul_nonneg (Nat.cast_nonneg _) (hφ0 β)) this
      exact_mod_cast this
  obtain ⟨h, hh⟩ := GlobalTheory.T.polarization_refined_fan_local E H D l Xo c X d k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol R ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn ℓ hℓ0
  have hJ := GlobalTheory.T.blowup_divisor_local_equation E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB R ξ t mξ P k' γ
    hCN hEt hFU hTI hCone hIn ℓ hℓ' h hh
  have hmℓ : (m : ℤ) = ℓ be := by
    have h1 : (m : ℝ) = ((n * d' : ℕ) : ℝ) * φ.evalZ be := by
      rw [hm]
      simp only [InvFun.evalZ, InvFun.eval, comb]
      push_cast
      ring
    have h2 : ((m : ℤ) : ℝ) = (ℓ be : ℝ) := by rw [hℓbe]; push_cast; rw [h1]; push_cast; ring
    exact_mod_cast h2
  obtain ⟨u, hu⟩ := hh W hW ϖ hϖ f be hbal.1 hFA m hmℓ
  rw [Ideal.span_le, Set.singleton_subset_iff, ← hu]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hJ)

end GlobalTheory.MixedLower
