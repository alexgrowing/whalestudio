import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleInvertibleSectionsLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionCuttingDivisorStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenPow

theorem gen_pow_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k : ℕ) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) →
    ∃ n : ℕ, 0 < n ∧ ∀ y : gen Y, ∃ (U : (gen X).affineOpens) (B : (gen Y).affineOpens) (hB : B.1 ≤ ρ ⁻¹ᵁ U.1)
      (T : Set Γ(gen Y, ρ ⁻¹ᵁ U.1)), y ∈ B.1 ∧
      (∀ t ∈ T, ∀ (A : (gen Y).affineOpens) (hA : A.1 ≤ ρ ⁻¹ᵁ U.1),
        resG (gen Y) hA t ∈ ((BY.idealSheaf ^ n).comap (genι Y)).ideal A) ∧
      ((BY.idealSheaf ^ n).comap (genι Y)).ideal B = Ideal.span (resG (gen Y) hB '' T) := by
  intro E _ _ _ H D l Xo c X Y BY k ρ hρ hY
  have hM : (GlobalTheory.FlagMod.detOm Y).IsLB := GlobalTheory.CechPic.isLB_dual (GlobalTheory.PolFin.isLB_detLie_of_polOf hY.isLB)
  obtain ⟨N, hN, K, s, hs, -⟩ := hY.exists_cover
  refine ⟨N, hN, fun y => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (genι Y y)))
  obtain ⟨U, hU, e, he, heu⟩ := GlobalTheory.T.det_bundle_invertible_sections_local E H D l Xo c X Y ρ hρ hM y
  obtain ⟨t, ht₁, ht₂⟩ := GlobalTheory.T.exists_function_cutting_divisor (genι Y) (GlobalTheory.FlagMod.detOm Y) BY k N (s i) (ρ ⁻¹ᵁ U.1) e hM he heu
  obtain ⟨B, hyB, hB'⟩ := GlobalTheory.EffCartierData.exists_affine_le
    (V := ρ ⁻¹ᵁ U.1 ⊓ genι Y ⁻¹ᵁ nonzeroLocus (s i)) (x := y) ⟨hU, hi⟩
  refine ⟨U, B, hB'.trans inf_le_left, {t}, hyB, ?_, ?_⟩
  · rintro t' rfl A hA'
    exact ht₁ A hA'
  · rw [Set.image_singleton]
    exact ht₂ B _ (hB'.trans inf_le_right)

end GlobalTheory.GenPow
