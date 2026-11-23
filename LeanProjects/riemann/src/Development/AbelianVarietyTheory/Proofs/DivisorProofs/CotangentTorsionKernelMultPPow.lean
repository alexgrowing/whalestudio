import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityFamily
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

theorem ker_cnθ_le : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), Module.Finite R (Wmod G) → Module.Projective R (Wmod G) → (∀ l : Wmod G →ₗ[R] R, ∃ (v : TM R R ⟶ G) (h : zeroSec R R ≫ v = η[G]), ∀ w, Phi v h w = l w) → SpecProp θ n hs → ∀ w : Wmod G, cnθ θ n hs w = 0 → w ∈ (Ideal.span {(p : R) ^ n} • ⊤ : Submodule R (Wmod G)) := by
  intro p _ O _ A _ G θ n hs hfin hproj hsurj hcn w hw
  refine GlobalTheory.LieKer.mem_smul_top_of_forms _ w fun l => ?_
  obtain ⟨v, hv, hl⟩ := hsurj l
  let M := ModPow p O n
  let mk : O →ₗ[O] M := (Ideal.Quotient.mkₐ O (Ideal.span {(p : O) ^ n})).toLinearMap
  have h' : zeroSec O M ≫ (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) = η[A] := by
    rw [← Category.assoc, GlobalTheory.LieKer.zeroSec_sqZeroMap, hv]
  have e1 := GlobalTheory.SqZeroPt.Phi_sqZeroMap_comp O O M A mk v hv h' w
  have htan : IsTangent v := by
    have := congrArg Over.Hom.left hv
    simp only [Over.comp_left, zeroSec, Over.homMk_left] at this
    exact this
  have hpow : (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v : SpAlg O (TrivSqZeroExt O M) ⟶ A) ^ p ^ n = 1 := by
    have hs : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale (((p ^ n : ℕ) : O)) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      ext1
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      ext
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR]
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mk]
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp htan, ← Category.assoc, hs,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp htan, MonObj.comp_one]
  have e2 := hcn M ⟨GlobalTheory.GrpTangent.sqZeroMap mk ≫ v, hpow⟩ h' w
  rw [hw, map_zero] at e2
  have e3 : mk (l w) = 0 := by rw [← hl, ← e1]; exact e2
  exact (Ideal.Quotient.eq_zero_iff_mem).1 e3

end GlobalTheory.OpenOmega
