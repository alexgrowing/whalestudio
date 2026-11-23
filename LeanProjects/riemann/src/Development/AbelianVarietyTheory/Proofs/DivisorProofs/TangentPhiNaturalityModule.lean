import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem Phi_congr {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A] {z z' : TM O M ⟶ A} (e : z = z')
    (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]) (w : Wmod A) :
    Phi z h w = Phi z' h' w := by
  subst e; rfl

theorem eq_map_comp_univ {p : ℕ} {O : Type} [CommRing O] (G : GlobalTheory.PDivGroup p O) {M : Type}
    [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ)
    (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
    (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) :
    φ = (TrivSqZeroExt.map
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)).comp (univ G n) := by
  have hf : ∀ a, (φ a).fst = Bialgebra.counitAlgHom O (G.A n) a := fun a => AlgHom.congr_fun hφ a
  ext a
  · simp [univ, hf]
  · simp [univ]

theorem Phi_spOver_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) := by
  intro p O _ G A _ t nat M _ _ _ _ n φ hφ w
  have e : spOver φ ≫ t.y n = GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n := by
    rw [← Category.assoc]
    congr 1
    have e1 : GlobalTheory.GrpTangent.sqZeroMap
        (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) =
        spOver (TrivSqZeroExt.map
          (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)) := rfl
    rw [e1, spOver_comp, ← eq_map_comp_univ G n φ hφ]
  have h' : zeroSec O M ≫ GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n = η[A] := e ▸ zeroSec_spOver_y t n φ hφ
  rw [Phi_congr e _ h' w]
  exact nat _ M _ (spOver (univ G n) ≫ t.y n)
    (zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)) h' w

end GlobalTheory.SqZeroPt
