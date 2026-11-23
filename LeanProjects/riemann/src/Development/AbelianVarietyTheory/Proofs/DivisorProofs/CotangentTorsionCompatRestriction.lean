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

theorem cotMap_res_cnθ : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) (hs' : PtSurj θ (n + 1)), SpecProp θ (n + 1) hs' → ∀ w : Wmod G, cotMap (GG.res n) (cnθ θ (n + 1) hs' w) = cnθ θ n hs w := by
  intro p _ R _ G _ GG θ n hs hs' hspec w
  let z' : Tors G (p ^ (n + 1)) (TrivSqZeroExt R (Cot R (GG.A n))) :=
    ⟨(univPt θ n hs).1, by rw [pow_succ, pow_mul, (univPt θ n hs).2, one_pow]⟩
  have hz' : zeroSec R (Cot R (GG.A n)) ≫ z'.1 = η[G] := (univPt_spec θ n hs).1
  have hpt : θ.pt (n + 1) _ z' = (univ GG n).comp (GG.res n : GG.A (n + 1) →ₐ[R] GG.A n) := by
    rw [θ.res n _ (univPt θ n hs) z' rfl, (univPt_spec θ n hs).2]
  have hlin : AugCot.sqZeroEquiv (Bialgebra.counitAlgHom R (GG.A (n + 1))) (Cot R (GG.A n))
      ⟨θ.pt (n + 1) _ z', fst_comp_pt θ (n + 1) z' hz'⟩ = cotMap (GG.res n) :=
    AugCot.hom_ext fun a => by
      rw [AugCot.sqZeroEquiv_d]
      refine Eq.trans ?_ (cotMap_d (GG.res n) a).symm
      change (θ.pt (n + 1) _ z' a).snd = _
      rw [hpt]
      simp [univ]
  have h := hspec _ z' hz' w
  rw [hlin] at h
  exact h.symm

end GlobalTheory.OpenOmega
