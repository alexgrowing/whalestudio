import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityModule
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

theorem comp_pow_eq_one {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {X Y : Over (Sp R)} (f : X ⟶ Y)
    (z : Y ⟶ G) {N : ℕ} (h : z ^ N = 1) : (f ≫ z) ^ N = 1 := by
  rw [← MonObj.comp_pow, h, MonObj.comp_one]

theorem specProp_of_ptInj : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), PtInj θ n → SpecProp θ n hs := by
  intro p _ R _ G _ GG θ n hs hi M _ _ _ _ z hz w
  have hφ := fst_comp_pt θ n z hz
  have e0 := eq_map_comp_univ GG n (θ.pt n _ z) hφ
  generalize AugCot.sqZeroEquiv (Bialgebra.counitAlgHom R (GG.A n)) M ⟨θ.pt n _ z, hφ⟩ = l at e0 ⊢
  have hu := univPt_spec θ n hs
  have h' : zeroSec R M ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ (univPt θ n hs).1) = η[G] := by
    rw [← Category.assoc, zeroSec_sqZeroMap, hu.1]
  let z' : Tors G (p ^ n) (TrivSqZeroExt R M) :=
    ⟨GlobalTheory.GrpTangent.sqZeroMap l ≫ (univPt θ n hs).1, comp_pow_eq_one _ _ (univPt θ n hs).2⟩
  have e1 : θ.pt n _ z' = (TrivSqZeroExt.map l).comp (θ.pt n _ (univPt θ n hs)) :=
    θ.nat n _ _ (TrivSqZeroExt.map l) (univPt θ n hs) z' rfl
  have e : z = z' := hi M z z' hz h' (by rw [e1, hu.2]; exact e0)
  rw [Phi_congr (congrArg Subtype.val e) hz h' w]
  exact Phi_sqZeroMap_comp R _ M G l (univPt θ n hs).1 hu.1 h' w

end GlobalTheory.OpenOmega
