import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSectionsOfNonzeroSpecial
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.PrimitiveExpansion

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem main : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  intro hL V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U σ ⟨x, hx, hn⟩
  obtain ⟨g, hE, hnd, H⟩ := GlobalTheory.NonzeroClosedFibre.main hL.1.globalFns V ϖ hϖ D Q hQ A G U σ
    (ThetaUnit.nonzeroOnSpecial_of_mem U σ x hx hn)
  have hgen := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd hL.1.secBaseChange V ϖ hϖ D (g 0)
    (fun ⟨g', h'⟩ => hnd ⟨g', fun j => (h' j).trans rfl⟩)
  refine ⟨fun s => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨Φ, hΦ, -⟩ := H (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ) (GlobalTheory.FamInt.valOver_ordVal hϖ)
    obtain ⟨b, hb⟩ := ThetaUnit.exists_eq_smul_group hL.1.globalFns le_rfl U hE
      (fun α => (ThetaUnit.secScal_one_iff D.toPre Φ α _).1 (hΦ α))
      (fun t => (hgen t).exists.imp fun b hb => (ThetaUnit.secIsMul_iff _ _ _ _).1 hb) s
    exact ⟨b, (ThetaUnit.secIsMul_iff _ _ _ _).2 hb⟩
  · obtain ⟨ϑ, hϑ, h₀, h₁⟩ := H F v hv
    refine ⟨ϑ, ⟨1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hE, secLin_one _
      (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_), fun α => secLin_one _ (hϑ α)⟩, h₀,
      fun r hr h => h₁ ⟨r, hr, h⟩⟩
    rw [Category.id_comp]
    exact (hσ' y J hJ).symm

end GlobalTheory.Ex.PrimitiveExpansion
end
