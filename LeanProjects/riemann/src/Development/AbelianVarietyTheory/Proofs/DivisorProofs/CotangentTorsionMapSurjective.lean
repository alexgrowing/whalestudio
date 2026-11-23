import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

namespace GlobalTheory.OpenOmega

theorem cnθ_surjective : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), (∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (z z' : TM R M ⟶ G) (h : zeroSec R M ≫ z = η[G]) (h' : zeroSec R M ≫ z' = η[G]), (∀ w, Phi z h w = Phi z' h' w) → z = z') → SpecProp θ n hs → Function.Surjective (cnθ θ n hs) := by
  intro p _ R _ G _ GG θ n hs hinj hspec
  let ε := Bialgebra.counitAlgHom R (GG.A n)
  let c : Wmod G →ₗ[R] AugCot ε := cnθ θ n hs
  let N := AugCot ε ⧸ LinearMap.range c
  letI : Module Rᵐᵒᵖ N := GlobalTheory.SqZeroPt.opModule R N
  haveI : IsCentralScalar R N := GlobalTheory.SqZeroPt.opModule_central R N
  let q : AugCot ε →ₗ[R] N := (LinearMap.range c).mkQ
  let φ := (AugCot.sqZeroEquiv ε N).symm q
  let φ₀ := (AugCot.sqZeroEquiv ε N).symm 0
  obtain ⟨z, hz, ez⟩ := hs N φ.1 φ.2
  obtain ⟨z₀, hz₀, ez₀⟩ := hs N φ₀.1 φ₀.2
  have e1 : z.1 = z₀.1 := hinj N _ _ hz hz₀ fun w => by
    refine (hspec N z hz w).trans (Eq.trans ?_ (hspec N z₀ hz₀ w).symm)
    have a1 : (⟨θ.pt n _ z, fst_comp_pt θ n z hz⟩ : {ψ : GG.A n →ₐ[R] TrivSqZeroExt R N //
        (TrivSqZeroExt.fstHom R R N).comp ψ = ε}) = φ := Subtype.ext ez
    have a2 : (⟨θ.pt n _ z₀, fst_comp_pt θ n z₀ hz₀⟩ : {ψ : GG.A n →ₐ[R] TrivSqZeroExt R N //
        (TrivSqZeroExt.fstHom R R N).comp ψ = ε}) = φ₀ := Subtype.ext ez₀
    refine (congrArg (fun ψ => AugCot.sqZeroEquiv ε N ψ (c w)) a1).trans
      (Eq.trans ?_ (congrArg (fun ψ => AugCot.sqZeroEquiv ε N ψ (c w)) a2).symm)
    change AugCot.sqZeroEquiv ε N φ (c w) = AugCot.sqZeroEquiv ε N φ₀ (c w)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  have e : φ.1 = φ₀.1 := ez.symm.trans ((congrArg (θ.pt n _) (Subtype.ext e1)).trans ez₀)
  have hq : q = 0 := (AugCot.sqZeroEquiv ε N).symm.injective (Subtype.ext e)
  intro x
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range c)).1 (LinearMap.congr_fun hq x)

end GlobalTheory.OpenOmega
