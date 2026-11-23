import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatementsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I}
  {π : R →+* R₀}

theorem canonical_of_free_hodge_baseChange_rigid (PF : AbelianDeRham.Free)
    (PH : AbelianDeRham.Hodge) (PB : AbelianDeRham.BaseChange) (PR : AbelianDeRham.Rigid)
    (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Canonical κ π := by
  intro g A₀ _ A _ i h hA hg
  letI : Algebra R R₀ := π.toAlgebra
  obtain ⟨-, ⟨N, hN⟩, -⟩ := PH R A g hA hg
  have hF : PrimitiveSubmodule A₀ = Submodule.span R₀ ((redMor h).pull '' (PrimitiveSubmodule A)) :=
    (PB R A g hA hg R₀ A₀ i h).2
  have := (PF.prim hA hg).2.1
  refine ⟨PR R A g hA hg I κ hκ R₀ π hπ hI A₀ i h, ⟨N.dualAnnihilator, ?_, ?_⟩, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, Fil, ← Submodule.dualAnnihilator_sup_eq, hN.sup_eq_top,
      Submodule.dualAnnihilator_top]
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ Submodule.mem_sup.2
      ⟨x ∘ₗ Submodule.projection _ _ hN.symm, ?_, x ∘ₗ Submodule.projection _ _ hN, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero]
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN).2 hc, map_zero]
    · ext c
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add, add_comm,
        Submodule.projection_add_projection_eq_self hN]
  · intro hy
    let l : primDR A →ₗ[R] R₀ :=
      { toFun c := y ((redMor h).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨x ∘ₗ Submodule.projection _ _ hN.symm, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero], fun c ↦ ?_⟩
    have z : l (Submodule.projection _ _ hN c) = 0 := (Submodule.mem_dualAnnihilator _).1 hy _
      (hF ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    change l c = π (x _)
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add, z, zero_add, ← hx]
    rfl
  · rintro ⟨x, hx, e⟩
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker y)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero])

end GrothendieckMessing

theorem grothendieckDeformation_of_structure (hS : AbelianDeRhamStructure)
    (hC : CrystallineDeRham) (hLift : AbelianLifting) : GrothendieckDeformation :=
  have hF : AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hS.1
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_free_hodge_baseChange_rigid hF hS.2.1 hS.2.2
      (AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hC) hκ hπ hI,
      hLift R I κ hκ R₀ π hπ hI⟩

theorem grothendieckDeformation_of_abelianLifting
    (hCrys : CrystallineSmoothLift) (hHdR : AbelianHodgeDeRham) (hLift : AbelianLifting) :
    GrothendieckDeformation :=
  grothendieckDeformation_of_structure (GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements hCrys hHdR).1 (GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements hCrys hHdR).2 hLift

theorem grothendieckDeformation₂
    (hCrys : CrystallineSmoothLift) (hHdR : AbelianHodgeDeRham) (_hDual : DualAbelianScheme)
    (_hPoinc : PoincareDeRhamDuality) (hLift : AbelianLifting) : GrothendieckDeformation :=
  grothendieckDeformation_of_abelianLifting hCrys hHdR hLift

example : CrystallineSmoothLift → AbelianHodgeDeRham → DualAbelianScheme →
    PoincareDeRhamDuality → AbelianLifting → GrothendieckDeformation :=
  grothendieckDeformation₂

end GlobalTheory.Published
