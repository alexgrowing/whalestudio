import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.FlagCell2.Dim

theorem card_low (s : ℕ) : Fintype.card (Low s) = s.choose 2 := by
  have h₁ : Fintype.card (Low s) = ∑ i : Fin s, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  rw [h₁, Nat.choose_two_right]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => s - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem dim_eq_of_refines {F : Type} [Field F] [CharZero F] {X Y Y' : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X}
    {S' : Fr (ratOf Y') m m} {φ' : X.Fn →ₐ[F] Y'.Fn} {f' : Y'.X ⟶ X.X}
    (hR : Refines E S φ f) (hR' : Refines E S' φ' f') : Y.dim = Y'.dim := by
  have R₁ := hR.reps
  have R₂ := hR'.reps
  obtain ⟨ψ, hψ, hG⟩ := exists_fieldMap_coBear_generic F ι m X Y Y' E S φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') Y.Fn (ratOf Y) ψ
    (dominates_O F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique R₁.1
  have hb := CoBear₂ F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ h hf
    (coBear_comp_of_isHom F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG h hh)
  change Y.X ⟶ Y'.X at h
  have : IsIso h := GlobalTheory.BijPointsIso.isIso_of_bijective_points F Y Y' h hh.inducedModelMorphism_comp_structureMap fun K _ _ => hb K
  have hd : topologicalKrullDim Y.X = topologicalKrullDim Y'.X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  rw [Y.topologicalKrullDim_eq, Y'.topologicalKrullDim_eq] at hd
  exact_mod_cast hd

theorem main : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  intro F _ σ X Y ι _ m E E' φ f _ hR
  have : CharZero F := σ.charZero
  obtain ⟨Y', φ', f', S', hd, hR'⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  rw [dim_eq_of_refines hR hR', hd, Fintype.card_sigma]
  simp only [card_low, Pi.zero_apply, Nat.sub_zero]

end GlobalTheory.FlagCell2.Dim
