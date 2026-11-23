import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraicStatement

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CMModel

theorem exists_model_of_lattice : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
        (U : Unif φ (lattice c y) 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p ∧
        (∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
        (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀)) ∧
        (∀ b : E, (∀ x ∈ lattice c y, b * x ∈ lattice c y) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
          ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) ∧
        ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
          ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨𝔠, X, U, hU⟩ := GlobalTheory.T.cm_abelian_variety_uniformization_exists K d δ io hK hd hδ E I φ hφ hio c y hc
  obtain ⟨X₀, p, hp⟩ := GlobalTheory.T.cm_abelian_variety_period_normalization hPC hDR hDC K d δ io hK hd hδ E I φ hφ hio c y hc 𝔠 X U
  obtain ⟨v₀, v, a, hv⟩ := GlobalTheory.T.cm_period_ratio_algebraic hPC hDR hDC K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc 𝔠 X U X₀ p hp
  refine ⟨𝔠, X₀, X, p, U, v₀, v, a, hp, hU, hv, ?_, ?_⟩
  · intro b hb
    let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j ↦ φ (U.e j) b * w j
        map_add' := fun w w' ↦ by funext j; simp [mul_add]
        map_smul' := fun r w ↦ by funext j; simp; ring }
    obtain ⟨α, hα, hex⟩ := GlobalTheory.T.lattice_preserving_map_gives_endomorphism (FR E) 𝔠 X _ _ U.u T (by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
      refine (U.lat _).2 ⟨b * x, hb x hx, ?_⟩
      funext j
      simp [T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord])
    exact ⟨α, hα, fun w' ↦ hex w'⟩
  · intro b α _ _
    exact GlobalTheory.T.endomorphism_descends_to_algebraic_model (FR E) 𝔠 X₀ X p hp α

end GlobalTheory.CMModel
