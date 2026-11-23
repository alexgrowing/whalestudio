import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.TauNorm

theorem valF_id {F : Type} [Field F] (U : (Sp F).Opens) (h : ⊤ ≤ U) (f : Γ(Sp F, U)) :
    valF (𝟙 (Sp F)) U f =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
        (((Sp F).presheaf.map (homOfLE h).op).hom f) := by
  have h' : ⊤ ≤ (𝟙 (Sp F) : Sp F ⟶ Sp F) ⁻¹ᵁ U := h
  unfold valF
  rw [dif_pos h']
  congr 1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem norm_psiCoord (u : ρ.UTest p y₀) (l : u.Lab) (χ : u.D.toPre.X)
    (x : (FractionRing u.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord u.D.toPre χ x) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ =
      Real.exp (-l.q χ) := by
  obtain ⟨j, h, hj, rfl⟩ := hx
  have := l.q_eq χ j hj
  rw [valF_id _ h] at this
  exact this

theorem norm_unit (u : ρ.UTest p y₀) (w : (u.V)ˣ) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ = 1 := by
  have h1 := (u.norm_le (algebraMap u.V (FractionRing u.V) (w : u.V))).2 ⟨_, rfl⟩
  have h2 := (u.norm_le (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))).2 ⟨_, rfl⟩
  have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ *
      ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a b : u.D.toPre.X) (x : (FractionRing u.V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord u.D.toPre a b x → ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ = Real.exp (-(l.q (a + b) - l.q a - l.q b)) := by
  intro o Ω _ _ _ S ρ p _ y₀ u l a b x hx
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre (a + b)
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre b
  obtain ⟨w, hw⟩ := GlobalTheory.TauCoordQuot.main u.V u.D.toPre a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  rw [hw, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, norm_mul, norm_mul, norm_mul,
    norm_inv, norm_inv, norm_unit, norm_psiCoord u l _ _ h₁, norm_psiCoord u l _ _ h₂,
    norm_psiCoord u l _ _ h₃, _root_.one_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

end GlobalTheory.Poinc.TauNorm
