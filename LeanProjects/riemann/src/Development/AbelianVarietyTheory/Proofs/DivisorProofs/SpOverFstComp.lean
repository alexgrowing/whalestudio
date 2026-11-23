import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
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

namespace GlobalTheory.OpenOmega

variable {p : ℕ} {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {GG : PDivGroup p R}

theorem spOver_fst_comp {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (z : SpAlg R (TrivSqZeroExt R M) ⟶ G) (hz : zeroSec R M ≫ z = η[G]) :
    spOver (TrivSqZeroExt.fstHom R R M) ≫ z = 1 := by
  have h2 := congrArg Over.Hom.left hz
  simp only [Over.comp_left] at h2
  ext1
  simp only [Over.comp_left]
  change (zeroSec R M).left ≫ z.left = _
  rw [h2]
  have hu : (toUnit (Over.mk (spMap (algebraMap R R)))).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]; exact Spec.map_id _
  change _ = (toUnit (Over.mk (spMap (algebraMap R R)))).left ≫ η[G].left
  erw [hu]
  exact (Category.id_comp _).symm

theorem fst_comp_pt [Fact p.Prime] (θ : TorsionMap G GG) (n : ℕ) {M : Type} [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (z : Tors G (p ^ n) (TrivSqZeroExt R M)) (hz : zeroSec R M ≫ z.1 = η[G]) :
    (TrivSqZeroExt.fstHom R R M).comp (θ.pt n _ z) = Bialgebra.counitAlgHom R (GG.A n) := by
  have h := θ.nat n (TrivSqZeroExt R M) R (TrivSqZeroExt.fstHom R R M) z ⟨1, one_pow _⟩
    (spOver_fst_comp z.1 hz).symm
  rw [← h]
  have h1 := θ.pt_one n R (Fact.out : p.Prime).ne_zero
  ext a
  have h2 := congrArg (fun f : WithConv (GG.A n →ₐ[R] R) => f.ofConv a) h1
  simpa using h2

def PtInj (θ : TorsionMap G GG) (n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (z z' : Tors G (p ^ n) (TrivSqZeroExt R M)), zeroSec R M ≫ z.1 = η[G] → zeroSec R M ≫ z'.1 = η[G] →
      θ.pt n _ z = θ.pt n _ z' → z = z'

def PtSurj (θ : TorsionMap G GG) (n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (φ : GG.A n →ₐ[R] TrivSqZeroExt R M), (TrivSqZeroExt.fstHom R R M).comp φ = Bialgebra.counitAlgHom R (GG.A n) →
      ∃ z : Tors G (p ^ n) (TrivSqZeroExt R M), zeroSec R M ≫ z.1 = η[G] ∧ θ.pt n _ z = φ

def univPt (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) : Tors G (p ^ n) (TrivSqZeroExt R (Cot R (GG.A n))) :=
  Classical.choose (hs _ (univ GG n) (fst_comp_univ n))

theorem univPt_spec (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) :
    zeroSec R (Cot R (GG.A n)) ≫ (univPt θ n hs).1 = η[G] ∧ θ.pt n _ (univPt θ n hs) = univ GG n :=
  Classical.choose_spec (hs _ (univ GG n) (fst_comp_univ n))

def cnθ (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) : Wmod G →ₗ[R] Cot R (GG.A n) where
  toFun := Phi (univPt θ n hs).1 (univPt_spec θ n hs).1
  map_add' := map_add _
  map_smul' a w := GlobalTheory.SqZeroPt.CnSurj.Phi_smul _ _ a w

theorem cnθ_apply (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) (w : Wmod G) :
    cnθ θ n hs w = Phi (univPt θ n hs).1 (univPt_spec θ n hs).1 w := rfl

def SpecProp [Fact p.Prime] (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (z : Tors G (p ^ n) (TrivSqZeroExt R M)) (hz : zeroSec R M ≫ z.1 = η[G]) (w : Wmod G),
      Phi z.1 hz w = AugCot.sqZeroEquiv (Bialgebra.counitAlgHom R (GG.A n)) M
        ⟨θ.pt n _ z, fst_comp_pt θ n z hz⟩ (cnθ θ n hs w)

end GlobalTheory.OpenOmega
