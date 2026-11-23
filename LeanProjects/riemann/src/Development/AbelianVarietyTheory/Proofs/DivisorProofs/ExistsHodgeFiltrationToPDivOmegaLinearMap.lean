import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_hodge_to_omega : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A),
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega, ∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c)) := by
  intro p _ R _ N hN A _ hA G t
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap R A p G t hA
  have hinj := GlobalTheory.PDivGroup.rigOfOmega_injective_of_pow p R N hN G
  have hmem : ∀ c : PrimitiveSubmodule A, (L ∘ₗ (PrimitiveSubmodule A).subtype) c ∈ LinearMap.range G.rigOfOmega := by
    intro c
    have hc : c.1.1 ∈ F1 (A.hom ≫ 𝟙 _) := c.2
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨β, hβ⟩ := hc
    have hβp : Form.cl _ β ∈ primDR A := hβ ▸ c.1.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.PtExt.isCan_form R A p G t β hβp
    have hcc : (⟨_, hβp⟩ : primDR A) = c.1 := Subtype.ext hβ
    rw [hcc] at hw
    exact ⟨w, ((hL _ _).1 hw).symm⟩
  refine ⟨(LinearEquiv.ofInjective G.rigOfOmega hinj).symm ∘ₗ
    (L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem, fun c ↦ ?_⟩
  rw [hL]
  have := (LinearEquiv.ofInjective G.rigOfOmega hinj).apply_symm_apply
    ((L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem c)
  exact (congrArg Subtype.val this).symm
