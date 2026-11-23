import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolOrdPull

theorem idlAlong_pull {X Y : Scheme.{0}} (D : GlobalTheory.EffCartierData X) (π : Y ⟶ X) (h : D.KeepsRegular π)
    {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ Y) :
    idlAlong (D.pull π h).idealSheaf y = idlAlong D.idealSheaf (y ≫ π) := by
  obtain ⟨k, hk⟩ := D.exists_mem ((y ≫ π) (closedPoint A))
  have hk' : ⊤ ≤ (y ≫ π) ⁻¹ᵁ D.U k := (Scheme.preimage_eq_top_of_closedPoint_mem _ hk).ge
  have hk'' : ⊤ ≤ y ⁻¹ᵁ (D.pull π h).U k := hk'
  rw [GlobalTheory.TraitGen.idlAlong_idealSheaf_eq (D.pull π h) y k hk'', GlobalTheory.TraitGen.idlAlong_idealSheaf_eq D (y ≫ π) k hk']
  congr 2

end GlobalTheory.PolOrdPull

open GlobalTheory.PolOrdPull in
theorem GlobalTheory.TorRef.isPhiDiv_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (X : Model Xo c β) (Z : Model Xo c β') (π : Z.X ⟶ X.X) (ψ : InvFun (𝓞 E)) (DX : GlobalTheory.EffCartierData X.X) (h : DX.KeepsRegular π), Z.j ≫ π = X.j → Nonempty (SABMap Z.t X.t π) → IsPhiDiv ψ X DX → IsPhiDiv ψ Z (DX.pull π h) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' X Z π ψ DX h hj ⟨n⟩ hX
  intro W _ _ _ hW ϖ hϖ χ t m P hgen be hbe hmon
  obtain ⟨m₂, -⟩ := GlobalTheory.LevelCover.sab_comp m n rfl
  have hgen' : Set.range (jK W ≫ χ ≫ π) ⊆ Set.range X.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hgen ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    rw [← hj, Scheme.Hom.comp_apply, hz]
    rfl
  obtain ⟨k, hk, hI⟩ := hX W hW ϖ hϖ (χ ≫ π) t m₂ P hgen' be hbe hmon
  exact ⟨k, hk, (idlAlong_pull DX π h χ).trans hI⟩
