import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigiStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {A : Over (Sp R)}

theorem fv_form (β : Form (A.hom ≫ 𝟙 _)) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : fv β.1 D D' φ x = 0 :=
  β.2 (trivMap φ x) rfl rfl

variable [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def formDat (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) : Dat t ⟨_, hβ⟩ where
  f := β.1
  cl := rfl
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by simp [fv_form]
  h := 0
  res := fun n ↦ by simp [fv_form]

theorem isCan_form : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A),
    ∃ w : G.omega, (∀ n, w.1 n = cotVal β.1 (t.y n)) ∧ IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) := by
  intro R _ A _ p G t β hβ
  refine ⟨⟨(formDat t β hβ).om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t _ (formDat t β hβ) n⟩, fun n ↦ ?_,
    formDat t β hβ, 0, _, fun n ↦ ?_, fun _ ↦ rfl, rfl⟩
  · change cotVal β.1 (t.y n) - dUnit R (0 : G.A n) = _
    rw [dUnit, map_zero, sub_zero]
  · change (0 : _) = 0 - (fv β.1 _ _ _ _ - fv β.1 _ _ _ _ - fv β.1 _ _ _ _) - cobOne R (G.A n) 0
    simp [fv_form]

end GlobalTheory.PtExt
