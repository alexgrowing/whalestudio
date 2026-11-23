import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationModel

def modelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add, M.add]
  smul c v := by rw [map_smul, M.smul]

theorem exists_model (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) (g : ℕ) (M : LieModel G x (Fin g → R))
    (y : Sp R' ⟶ S) (hy : y = spMap c ≫ x) :
    ∃ Mz : LieModel G y (Fin g → R'), ∀ e : Fin g → R, M.Lifts c (𝟙 _) e (Mz.pt fun i => c (e i)) := by
  subst hy
  obtain ⟨F, _, _, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap c ≫ x)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R R' c x _ F M M'
  letI : Algebra R R' := c.toAlgebra
  letI : Module R F := Module.compHom F c
  haveI : IsScalarTower R R' F := ⟨fun r s f => by
    change (c r * s) • f = c r • s • f
    rw [mul_smul]⟩
  let j' : (Fin g → R) →ₗ[R] F :=
    { toFun := j, map_add' := j.map_add, map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' j' := lieModel_isBaseChange S G R R' x _ F M M' j' hj
  refine ⟨modelOfEquiv M' ((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv), fun e => ?_⟩
  have h1 : (TensorProduct.piScalarRight R R' R' (Fin g)).symm (fun i => c (e i)) = (1 : R') ⊗ₜ[R] e := by
    rw [LinearEquiv.symm_apply_eq, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    change c (e i) = c (e i) * 1
    rw [_root_.mul_one]
  have h2 : ((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv) (fun i => c (e i)) = j e := by
    rw [LinearEquiv.trans_apply, h1, IsBaseChange.equiv_tmul, one_smul]
    rfl
  change M.Lifts c (𝟙 _) e (M'.pt (((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv)
    (fun i => c (e i))))
  rw [h2]
  exact hj e

end PositivityTheory.Xgn.QuotientUniformizationModel

theorem PositivityTheory.Xgn.quotient_uniformization_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i)) := by
  intro E _ _ _ H D l Xo σ n a C u
  have := C.t.semi.smooth
  exact PositivityTheory.Xgn.QuotientUniformizationModel.exists_model _ C.t.G C.R ℂ (C.ψ u) (𝟙 _) C.g C.M _
    (Category.comp_id _).symm
