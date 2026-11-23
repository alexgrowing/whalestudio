import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfDualMapSurjectiveOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCompHodgeToOmegaEqLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtensionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem bijective_of_isCan_of_isNilpotent_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] G.RigExt), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  intro hH p _ R _ hnil A _ g hA hg G t L hL
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hHo, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hH
  obtain ⟨hAll, -⟩ := hF R A g hA hg
  obtain ⟨hLie, hCompl, hFfin, hFproj, -⟩ := hHo R A g hA hg
  have hO : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) :=
    GlobalTheory.PtExt.toH1O_surjective_of_abelian hH R A g hA hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t

  haveI : Module.Finite R (Cot R (G.A N)) := .of_surjective _ (AugCot.d_surjective _)
  haveI : Module.Finite R G.omega :=
    .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
  haveI : Module.Projective R (PrimitiveSubmodule A) := hFproj

  have hψs : Function.Surjective ψ :=
    GlobalTheory.surjective_of_range_sup_smul_top_eq_top R _ G.omega ψ
      (GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal hH p R N hN A g hA hg G t ψ hψ)
  have hψi : Function.Injective ψ := by
    refine GlobalTheory.injective_of_dualMap_surjective_of_projective R _ G.omega ψ fun l => ?_
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm p R N hN A hA hLie hCompl G t ψ hψ l
    exact ⟨x, LinearMap.ext fun c => hx c⟩

  have hLF : ∀ c : PrimitiveSubmodule A, L c.1 = G.rigOfOmega (ψ c) := fun c =>
    GlobalTheory.PtExt.isCan_unique R A p G t c.1 hA _ _ (hL c.1) (hψ c)
  refine ⟨(injective_iff_map_eq_zero L).2 fun c hc => ?_, fun x => ?_⟩
  · have hcF : c ∈ PrimitiveSubmodule A :=
      GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hL c) (by rw [hc, map_zero])
    have h1 : G.rigOfOmega (ψ ⟨c, hcF⟩) = 0 := by rw [← hLF ⟨c, hcF⟩]; exact hc
    have h2 : ψ ⟨c, hcF⟩ = 0 :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (by rw [h1, map_zero])
    have h3 : (⟨c, hcF⟩ : PrimitiveSubmodule A) = 0 := hψi (by rw [h2, map_zero])
    exact congrArg Subtype.val h3
  · obtain ⟨c, x', hcx', hx'⟩ := GlobalTheory.T.exists_deRham_class_of_rigidified_extension p R N hN A hA hAll hO G t x
    have hx'L : x' = L c := GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ hcx' (hL c)
    have hd : G.rigToExt (x - L c) = 0 := by rw [map_sub, ← hx'L, hx', sub_self]
    obtain ⟨w, hw⟩ := (G.exact_rigOfOmega_rigToExt (x - L c)).1 hd
    obtain ⟨c₁, rfl⟩ := hψs w
    refine ⟨c + c₁.1, ?_⟩
    rw [map_add, hLF c₁, hw, add_sub_cancel]

end GlobalTheory.PtExt
